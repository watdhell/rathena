// Copyright (c) rAthena Dev Teams - Licensed under GNU GPL
// For more information, see LICENCE in the main folder

#include "unit.hpp"

#include <cstdlib>
#include <cstring>

#include <common/db.hpp>
#include <common/ers.hpp>  // ers_destroy
#include <common/malloc.hpp>
#include <common/nullpo.hpp>
#include <common/random.hpp>
#include <common/showmsg.hpp>
#include <common/socket.hpp>
#include <common/timer.hpp>
#include <common/utils.hpp>

#include "achievement.hpp"
#include "battle.hpp"
#include "battleground.hpp"
#include "channel.hpp"
#include "chat.hpp"
#include "clif.hpp"
#include "duel.hpp"
#include "elemental.hpp"
#include "guild.hpp"
#include "homunculus.hpp"
#include "intif.hpp"
#include "map.hpp"
#include "mercenary.hpp"
#include "mob.hpp"
#include "npc.hpp"
#include "party.hpp"
#include "path.hpp"
#include "pc.hpp"
#include "pet.hpp"
#include "storage.hpp"
#include "trade.hpp"

using namespace rathena;

#ifndef MAX_SHADOW_SCAR 
	#define MAX_SHADOW_SCAR 100 /// Max Shadow Scars
#endif

// How many milliseconds need to pass before we calculated the exact position of a unit
// Calculation will only happen on demand and when at least the time defined here has passed
#ifndef MIN_POS_INTERVAL
	#define MIN_POS_INTERVAL 20
#endif

// Minimum delay after which new client-sided commands for slaves are accepted
// Applies to mercenaries and homunculus
#ifndef MIN_DELAY_SLAVE
	#define MIN_DELAY_SLAVE MAX_ASPD_NOPC * 2
#endif

// Time frame during which we will send move packets each cell moved after being hit
// This is needed because damage packets prevent the client from displaying movement for a while
#ifndef MOVE_REFRESH_TIME
	#define MOVE_REFRESH_TIME MAX_WALK_SPEED
#endif

// Directions values
// 1 0 7
// 2 . 6
// 3 4 5
// See also path.cpp walk_choices
const int16 dirx[DIR_MAX]={0,-1,-1,-1,0,1,1,1}; ///lookup to know where will move to x according dir
const int16 diry[DIR_MAX]={1,1,0,-1,-1,-1,0,1}; ///lookup to know where will move to y according dir

//early declaration
static TIMER_FUNC(unit_attack_timer);
static TIMER_FUNC(unit_walktoxy_timer);
int32 unit_unattackable(struct block_list *bl);

/**
 * Get the unit_data related to the bl
 * @param bl : Object to get the unit_data from
 *	valid type are : BL_PC|BL_MOB|BL_PET|BL_NPC|BL_HOM|BL_MER|BL_ELEM
 * @return unit_data of bl or nullptr
 */
struct unit_data* unit_bl2ud(struct block_list *bl)
{
	if( bl == nullptr) return nullptr;
	switch(bl->type){
	case BL_PC: return &((map_session_data*)bl)->ud;
	case BL_MOB: return &((struct mob_data*)bl)->ud;
	case BL_PET: return &((struct pet_data*)bl)->ud;
	case BL_NPC: return &((struct npc_data*)bl)->ud;
	case BL_HOM: return &((struct homun_data*)bl)->ud;
	case BL_MER: return &((s_mercenary_data*)bl)->ud;
	case BL_ELEM: return &((s_elemental_data*)bl)->ud;
	default : return nullptr;
	}
}

/**
 * Updates chase depending on situation:
 * If target in attack range -> attack
 * If target out of sight -> drop target
 * Otherwise update chase path
 * @param bl: Moving bl
 * @param tick: Current tick
 * @param fullcheck: If false, only check for attack, don't drop target or update chase path
 * @return Whether the chase path was updated (true) or current movement can continue (false)
 */
bool unit_update_chase(block_list& bl, t_tick tick, bool fullcheck) {
	unit_data* ud = unit_bl2ud(&bl);

	if (ud == nullptr)
		return true;

	block_list* tbl = nullptr;
	if (ud->target_to != 0)
		tbl = map_id2bl(ud->target_to);

	// Reached destination, start attacking
	if (tbl != nullptr && tbl->type != BL_ITEM && tbl->m == bl.m && ud->walkpath.path_pos > 0 && check_distance_bl(&bl, tbl, ud->chaserange)) {
		// We need to make sure the walkpath is cleared here so a monster doesn't continue walking in case it unlocks its target
		unit_stop_walking(&bl, USW_FIXPOS|USW_FORCE_STOP|USW_RELEASE_TARGET);
		if (ud->state.attack_continue)
			unit_attack(&bl, tbl->id, ud->state.attack_continue);
		return true;
	}
	// Cancel chase
	else if (tbl == nullptr || (fullcheck && !status_check_visibility(&bl, tbl, (bl.type == BL_MOB)))) {
		// Looted items will have no tbl but target ID is still set, that's why we need to check for the ID here
		if (ud->target_to != 0 && bl.type == BL_MOB) {
			mob_data& md = reinterpret_cast<mob_data&>(bl);
			if (tbl != nullptr) {
				int32 warp = mob_warpchase(&md, tbl);
				// Do warp chase
				if (warp == 1)
					return true;
				// Continue moving to warp
				else if (warp == 2)
					return false;
			}
			// Make sure monsters properly unlock their target, but still continue movement
			mob_unlocktarget(&md, tick);
			return false;
		}

		unit_stop_walking(&bl, USW_FIXPOS|USW_FORCE_STOP|USW_RELEASE_TARGET);
		return true;
	}
	// Update chase path
	else if (fullcheck && ud->walkpath.path_pos > 0 && DIFF_TICK(ud->canmove_tick, tick) <= 0) {
		// We call this only when we know there is no walk delay to prevent it pre-planning a chase
		// If the call here fails, the unit should continue its current path
		if(unit_walktobl(&bl, tbl, ud->chaserange, ud->state.walk_easy | (ud->state.attack_continue ? 2 : 0)))
			return true;
	}

	return false;
}

/**
 * Handles everything that happens when movement to the next cell is initiated
 * @param bl: Moving bl
 * @param sendMove: Whether move packet should be sent or not
 * @param tick: Current tick
 * @return Whether movement was initialized (true) or not (false)
 */
bool unit_walktoxy_nextcell(block_list& bl, bool sendMove, t_tick tick) {
	unit_data* ud = unit_bl2ud(&bl);

	if (ud == nullptr)
		return true;

	// Reached end of walkpath
	if (ud->walkpath.path_pos >= ud->walkpath.path_len) {
		// We need to send the reply to the client even if already at the target cell
		// This allows the client to synchronize the position correctly
		if (sendMove && bl.type == BL_PC)
			clif_walkok(reinterpret_cast<map_session_data&>(bl));
		return false;
	}

	// Monsters first check for a chase skill and if they didn't use one if their target is in range each cell after checking for a chase skill
	if (bl.type == BL_MOB) {
		mob_data& md = reinterpret_cast<mob_data&>(bl);
		// Walk skills are triggered regardless of target due to the idle-walk mob state.
		// But avoid triggering when already reached the end of the walkpath.
		// Monsters use walk/chase skills every second, but we only get here every "speed" ms
		// To make sure we check one skill per second on average, we substract half the speed as ms
		if (!ud->state.force_walk &&
			DIFF_TICK(tick, md.last_skillcheck) > MOB_SKILL_INTERVAL - md.status.speed / 2 &&
			mobskill_use(&md, tick, -1)) {
			if ((ud->skill_id != NPC_SPEEDUP || md.trickcasting == 0) //Stop only when trickcasting expired
				&& ud->skill_id != NPC_EMOTION && ud->skill_id != NPC_EMOTION_ON //NPC_EMOTION doesn't make the monster stop
				&& md.state.skillstate != MSS_WALK) //Walk skills are supposed to be used while walking
			{
				// Skill used, abort walking
				// Fix position as walk has been cancelled.
				clif_fixpos(bl);
				// Movement was initialized, so we need to return true even though it was stopped
				// Monsters only start moving or drop target when they stop using chase skills that stop them
				return true;
			}
			// Resend walk packet for proper Self Destruction display
			sendMove = true;
		}
		if (ud->target_to != 0) {
			// Monsters update their chase path one cell before reaching their final destination
			if (unit_update_chase(bl, tick, (ud->walkpath.path_pos == ud->walkpath.path_len - 1)))
				return true;
		}
	}

	// Get current speed
	int32 speed;
	if (direction_diagonal(ud->walkpath.path[ud->walkpath.path_pos]))
		speed = status_get_speed(&bl) * MOVE_DIAGONAL_COST / MOVE_COST;
	else
		speed = status_get_speed(&bl);

	// Make sure there is no active walktimer
	if (ud->walktimer != INVALID_TIMER) {
		delete_timer(ud->walktimer, unit_walktoxy_timer);
		ud->walktimer = INVALID_TIMER;
	}
	ud->walktimer = add_timer(tick + speed, unit_walktoxy_timer, bl.id, speed);

	// Resend move packet when unit was damaged recently
	if (sendMove || DIFF_TICK(tick, ud->dmg_tick) < MOVE_REFRESH_TIME) {
		clif_move(*ud);
		if (bl.type == BL_PC)
			clif_walkok(reinterpret_cast<map_session_data&>(bl));
	}
	return true;
}

/**
 * Tells a unit to walk to a specific coordinate
 * @param bl: Unit to walk [ALL]
 * @return 1: Success 0: Fail
 */
int32 unit_walktoxy_sub(struct block_list *bl)
{
	nullpo_retr(1, bl);

	unit_data *ud = unit_bl2ud(bl);

	if (ud == nullptr)
		return 0;

	walkpath_data wpd = { 0 };

	if( !path_search(&wpd,bl->m,bl->x,bl->y,ud->to_x,ud->to_y,ud->state.walk_easy,CELL_CHKNOPASS) )
		return 0;

#ifdef OFFICIAL_WALKPATH
	if( bl->type != BL_NPC // If type is a NPC, please disregard.
		&& wpd.path_len > 14 // Official number of walkable cells is 14 if and only if there is an obstacle between. [malufett]
		&& !path_search_long(nullptr, bl->m, bl->x, bl->y, ud->to_x, ud->to_y, CELL_CHKNOPASS) ) // Check if there is an obstacle between
			return 0;
#endif

	ud->walkpath = wpd;

	int32 i;

	// Monsters always target an adjacent tile even if ranged, no need to shorten the path
	if (ud->target_to != 0 && ud->chaserange > 1 && bl->type != BL_MOB) {
		// Generally speaking, the walk path is already to an adjacent tile
		// so we only need to shorten the path if the range is greater than 1.
		// Trim the last part of the path to account for range,
		// but always move at least one cell when requested to move.
		for (i = (ud->chaserange*10)-10; i > 0 && ud->walkpath.path_len>1;) {
			ud->walkpath.path_len--;
			enum directions dir = ud->walkpath.path[ud->walkpath.path_len];
			if (direction_diagonal(dir))
				i -= MOVE_COST * 2; //When chasing, units will target a diamond-shaped area in range [Playtester]
			else
				i -= MOVE_COST;
			ud->to_x -= dirx[dir];
			ud->to_y -= diry[dir];
		}
	}

	ud->state.change_walk_target=0;

	if (bl->type == BL_PC) {
		map_session_data *sd = BL_CAST(BL_PC, bl);
		sd->head_dir = DIR_NORTH;
	}
#if PACKETVER >= 20170726
	// If this is a walking NPC and it will use a player sprite
	else if( bl->type == BL_NPC && pcdb_checkid( status_get_viewdata( bl )->class_ ) ){
		// Respawn the NPC as player unit
		unit_refresh( bl, true );
	}
#endif
	// Set mobstate here already as chase skills can be used on the first frame of movement
	// If we don't set it now the monster will always move a full cell before checking
	else if (bl->type == BL_MOB && ud->state.attack_continue) {
		mob_data& md = reinterpret_cast<mob_data&>(*bl);
		mob_setstate(md, MSS_RUSH);
	}

	unit_walktoxy_nextcell(*bl, true, gettick());

	return 1;
}

/**
 * Retrieve the direct master of a bl if one exists.
 * @param bl: char to get his master [HOM|ELEM|PET|MER]
 * @return map_session_data of master or nullptr
 */
TBL_PC* unit_get_master(struct block_list *bl)
{
	if(bl)
		switch(bl->type) {
			case BL_HOM: return (((TBL_HOM *)bl)->master);
			case BL_ELEM: return (((TBL_ELEM *)bl)->master);
			case BL_PET: return (((TBL_PET *)bl)->master);
			case BL_MER: return (((TBL_MER *)bl)->master);
		}
	return nullptr;
}

/**
 * Retrieve a unit's master's teleport timer
 * @param bl: char to get his master's teleport timer [HOM|ELEM|PET|MER]
 * @return timer or nullptr
 */
int32* unit_get_masterteleport_timer(struct block_list *bl)
{
	if(bl)
		switch(bl->type) {
			case BL_HOM: return &(((TBL_HOM *)bl)->masterteleport_timer);
			case BL_ELEM: return &(((TBL_ELEM *)bl)->masterteleport_timer);
			case BL_PET: return &(((TBL_PET *)bl)->masterteleport_timer);
			case BL_MER: return &(((TBL_MER *)bl)->masterteleport_timer);
		}
	return nullptr;
}

/**
 * Warps a unit to its master if the master has gone out of sight (3 second default)
 * Can be any object with a master [MOB|PET|HOM|MER|ELEM]
 * @param tid: Timer
 * @param tick: tick (unused)
 * @param id: Unit to warp
 * @param data: Data transferred from timer call
 * @return 0
 */
TIMER_FUNC(unit_teleport_timer){
	struct block_list *bl = map_id2bl(id);
	int32 *mast_tid = unit_get_masterteleport_timer(bl);

	if(tid == INVALID_TIMER || mast_tid == nullptr)
		return 0;
	else if(*mast_tid != tid || bl == nullptr)
		return 0;
	else {
		map_session_data* msd = unit_get_master( bl );

		if( msd != nullptr && !check_distance_bl( &msd->bl, bl, static_cast<int32>( data ) ) ){
			*mast_tid = INVALID_TIMER;
			unit_warp(bl, msd->bl.m, msd->bl.x, msd->bl.y, CLR_TELEPORT );
		} else // No timer needed
			*mast_tid = INVALID_TIMER;
	}
	return 0;
}

/**
 * Checks if a slave unit is outside their max distance from master
 * If so, starts a timer (default: 3 seconds) which will teleport the unit back to master
 * @param sbl: Object with a master [MOB|PET|HOM|MER|ELEM]
 * @return 0
 */
int32 unit_check_start_teleport_timer(struct block_list *sbl)
{
	TBL_PC *msd = nullptr;
	int32 max_dist = 0;

	switch(sbl->type) {
		case BL_HOM:	
		case BL_ELEM:	
		case BL_PET:	
		case BL_MER:	
			msd = unit_get_master(sbl);
			break;
		default:
			return 0;
	}

	switch(sbl->type) {
		case BL_HOM:	max_dist = AREA_SIZE;			break;
		case BL_ELEM:	max_dist = MAX_ELEDISTANCE;		break;
		case BL_PET:	max_dist = AREA_SIZE;			break;
		case BL_MER:	max_dist = MAX_MER_DISTANCE;	break;
	}
	// If there is a master and it's a valid type
	if(msd && max_dist) {
		int32 *msd_tid = unit_get_masterteleport_timer(sbl);

		if(msd_tid == nullptr)
			return 0;
		if (!check_distance_bl(&msd->bl, sbl, max_dist)) {
			if(*msd_tid == INVALID_TIMER || *msd_tid == 0)
				*msd_tid = add_timer(gettick()+3000,unit_teleport_timer,sbl->id,max_dist);
		} else {
			if(*msd_tid && *msd_tid != INVALID_TIMER)
				delete_timer(*msd_tid,unit_teleport_timer);
			*msd_tid = INVALID_TIMER; // Cancel recall
		}
	}
	return 0;
}

/**
 * Triggered on full step if stepaction is true and executes remembered action.
 * @param tid: Timer ID
 * @param tick: Unused
 * @param id: ID of bl to do the action
 * @param data: Not used
 * @return 1: Success 0: Fail (No valid bl)
 */
TIMER_FUNC(unit_step_timer){
	struct block_list *bl;
	struct unit_data *ud;
	int32 target_id;

	bl = map_id2bl(id);

	if (!bl || bl->prev == nullptr)
		return 0;

	ud = unit_bl2ud(bl);

	if(!ud)
		return 0;

	if(ud->steptimer != tid) {
		ShowError("unit_step_timer mismatch %d != %d\n",ud->steptimer,tid);
		return 0;
	}

	ud->steptimer = INVALID_TIMER;

	if(!ud->stepaction)
		return 0;

	//Set to false here because if an error occurs, it should not be executed again
	ud->stepaction = false;

	if(!ud->target_to)
		return 0;

	//Flush target_to as it might contain map coordinates which should not be used by other functions
	target_id = ud->target_to;
	ud->target_to = 0;

	//If stepaction is set then we remembered a client request that should be executed on the next step
	//Execute request now if target is in attack range
	if(ud->stepskill_id && skill_get_inf(ud->stepskill_id) & INF_GROUND_SKILL) {
		//Execute ground skill
		struct map_data *md = &map[bl->m];			
		unit_skilluse_pos(bl, target_id%md->xs, target_id/md->xs, ud->stepskill_id, ud->stepskill_lv);
	} else {
		//If a player has target_id set and target is in range, attempt attack
		struct block_list *tbl = map_id2bl(target_id);
		if (tbl == nullptr || !status_check_visibility(bl, tbl, false)) {
			return 0;
		}
		if(ud->stepskill_id == 0) {
			//Execute normal attack
			unit_attack(bl, tbl->id, (ud->state.attack_continue) + 2);
		} else {
			//Execute non-ground skill
			unit_skilluse_id(bl, tbl->id, ud->stepskill_id, ud->stepskill_lv);
		}
	}

	return 1;
}

int32 unit_walktoxy_ontouch(struct block_list *bl, va_list ap)
{
	struct npc_data *nd;

	nullpo_ret(bl);
	nullpo_ret(nd = va_arg(ap,struct npc_data *));

	switch( bl->type ) {
	case BL_PC:
		TBL_PC *sd = (TBL_PC*)bl;

		if (sd == nullptr)
			return 1;
		if (sd->state.block_action & PCBLOCK_NPCCLICK)
			return 1;

		// Remove NPCs that are no longer within the OnTouch area
		for (size_t i = 0; i < sd->areanpc.size(); i++) {
			struct npc_data *nd = map_id2nd(sd->areanpc[i]);

			if (!nd || nd->subtype != NPCTYPE_SCRIPT || !(nd->bl.m == bl->m && bl->x >= nd->bl.x - nd->u.scr.xs && bl->x <= nd->bl.x + nd->u.scr.xs && bl->y >= nd->bl.y - nd->u.scr.ys && bl->y <= nd->bl.y + nd->u.scr.ys))
				rathena::util::erase_at(sd->areanpc, i);
		}
		npc_touchnext_areanpc(sd, false);

		if (map_getcell(bl->m, bl->x, bl->y, CELL_CHKNPC) == 0)
			return 1;

		npc_touch_areanpc(sd, bl->m, bl->x, bl->y, nd);
		break;
	// case BL_MOB:	// unsupported
	}
	
	return 0;
}

/**
 * Defines when to refresh the walking character to object and restart the timer if applicable
 * Also checks for speed update, target location, and slave teleport timers
 * @param tid: Timer ID
 * @param tick: Current tick to decide next timer update
 * @param data: Data used in timer calls
 * @return 0 or unit_walktoxy_sub() or unit_walktoxy()
 */
static TIMER_FUNC(unit_walktoxy_timer)
{
	block_list *bl = map_id2bl(id);

	if(bl == nullptr)
		return 0;
	
	unit_data *ud = unit_bl2ud(bl);

	if(ud == nullptr)
		return 0;

	if(ud->walktimer != tid) {
		ShowError("unit_walk_timer mismatch %d != %d\n",ud->walktimer,tid);
		return 0;
	}

	ud->walktimer = INVALID_TIMER;
	// As movement to next cell finished, set sub-cell position to center
	ud->sx = 8;
	ud->sy = 8;

	if (bl->prev == nullptr)
		return 0; // Stop moved because it is missing from the block_list

	if(ud->walkpath.path_pos>=ud->walkpath.path_len)
		return 0;

	enum directions dir = ud->walkpath.path[ud->walkpath.path_pos];

	if( dir <= DIR_CENTER || dir >= DIR_MAX ){
		return 0;
	}

	unit_setdir(bl, dir, false);

	int32 dx = dirx[dir];
	int32 dy = diry[dir];

	map_session_data *sd = nullptr;
	mob_data *md = nullptr;
	npc_data *nd = nullptr;

	// Get icewall walk block depending on Status Immune mode (players can't be trapped)
	unsigned char icewall_walk_block = 0;

	switch(bl->type) { // avoid useless cast, we can only be 1 type
		case BL_PC: sd = BL_CAST(BL_PC, bl); break;
		case BL_MOB:
			md = BL_CAST(BL_MOB, bl);

			if (status_has_mode(&md->status,MD_STATUSIMMUNE))
				icewall_walk_block = battle_config.boss_icewall_walk_block;
			else
				icewall_walk_block = battle_config.mob_icewall_walk_block;
			break;
		case BL_NPC: nd = BL_CAST(BL_NPC, bl); break;
	}

	int32 x = bl->x;
	int32 y = bl->y;

	//Monsters will walk into an icewall from the west and south if they already started walking
	if(map_getcell(bl->m,x+dx,y+dy,CELL_CHKNOPASS) 
		&& (icewall_walk_block == 0 || dx < 0 || dy < 0 || !map_getcell(bl->m,x+dx,y+dy,CELL_CHKICEWALL)))
		return unit_walktoxy_sub(bl);

	//Monsters can only leave icewalls to the west and south
	//But if movement fails more than icewall_walk_block times, they can ignore this rule
	if(md && !ud->state.force_walk && md->walktoxy_fail_count < icewall_walk_block && map_getcell(bl->m,x,y,CELL_CHKICEWALL) && (dx > 0 || dy > 0)) {
		//Needs to be done here so that rudeattack skills are invoked
		md->walktoxy_fail_count++;
		clif_fixpos( *bl );
		// Monsters in this situation will unlock target
		mob_unlocktarget(md, tick);
		return 0;
	}

	// Refresh view for all those we lose sight
	map_foreachinmovearea(clif_outsight, bl, AREA_SIZE, dx, dy, sd?BL_ALL:BL_PC, bl);

	x += dx;
	y += dy;
	map_moveblock(bl, x, y, tick);

	if (bl->x != x || bl->y != y || ud->walktimer != INVALID_TIMER)
		return 0; // map_moveblock has altered the object beyond what we expected (moved/warped it)

	ud->walktimer = CLIF_WALK_TIMER; // Arbitrary non-INVALID_TIMER value to make the clif code send walking packets
	map_foreachinmovearea(clif_insight, bl, AREA_SIZE, -dx, -dy, sd?BL_ALL:BL_PC, bl);
	ud->walktimer = INVALID_TIMER;

	if (bl->x == ud->to_x && bl->y == ud->to_y) {
#if PACKETVER >= 20170726
		// If this was a walking NPC and it used a player sprite
		if( bl->type == BL_NPC && pcdb_checkid( status_get_viewdata( bl )->class_ ) ){
			// Respawn the NPC as NPC unit
			unit_refresh( bl, false );
		}
#endif

		// Remove any possible escape states present for mobs once they stopped moving.
		if (md != nullptr) {
			md->state.can_escape = 0;
		}

		ud->state.force_walk = false;

		if (ud->walk_done_event[0]){
			char walk_done_event[EVENT_NAME_LENGTH];

			// Copying is required in case someone uses unitwalkto inside the event code
			safestrncpy(walk_done_event, ud->walk_done_event, EVENT_NAME_LENGTH);

			//Clear the event
			ud->walk_done_event[0] = 0;

			ud->state.walk_script = true;

			// Execute the event
			npc_event_do_id(walk_done_event,bl->id);

			ud->state.walk_script = false;

			// Check if the unit was killed
			if( status_isdead(*bl) ){
				struct mob_data* md = BL_CAST(BL_MOB, bl);

				if( md && !md->spawn ){
					unit_free(bl, CLR_OUTSIGHT);
				}

				return 0;
			}

		}
	}

	switch(bl->type) {
		case BL_PC:
			if( !sd->npc_ontouch_.empty() )
				npc_touchnext_areanpc(sd,false);
			if(map_getcell(bl->m,x,y,CELL_CHKNPC)) {
				npc_touch_area_allnpc(sd,bl->m,x,y);
				if (bl->prev == nullptr) // Script could have warped char, abort remaining of the function.
					return 0;
			} else
				sd->areanpc.clear();
			pc_cell_basilica(sd);
			break;
		case BL_MOB:
			//Movement was successful, reset walktoxy_fail_count
			md->walktoxy_fail_count = 0;
			if( map_getcell(bl->m,x,y,CELL_CHKNPC) ) {
				if( npc_touch_areanpc2(md) )
					return 0; // Warped
			} else
				md->areanpc_id = 0;
			break;
		case BL_NPC:
			if (nd->is_invisible)
				break;

			int32 xs = -1, ys = -1;
			switch (nd->subtype) {
			case NPCTYPE_SCRIPT:
				xs = nd->u.scr.xs;
				ys = nd->u.scr.ys;
				break;
			case NPCTYPE_WARP:
				xs = nd->u.warp.xs;
				ys = nd->u.warp.ys;
				break;
			}
			if (xs > -1 && ys > -1)
				map_foreachinmap(unit_walktoxy_ontouch, nd->bl.m, BL_PC, nd);
			break;
	}

	int32 speed;

	//If stepaction is set then we remembered a client request that should be executed on the next step
	if (ud->stepaction && ud->target_to) {
		//Delete old stepaction even if not executed yet, the latest command is what counts
		if(ud->steptimer != INVALID_TIMER) {
			delete_timer(ud->steptimer, unit_step_timer);
			ud->steptimer = INVALID_TIMER;
		}
		//Delay stepactions by half a step (so they are executed at full step)
		if( direction_diagonal( ud->walkpath.path[ud->walkpath.path_pos] ) )
			speed = status_get_speed(bl)*MOVE_DIAGONAL_COST/MOVE_COST/2;
		else
			speed = status_get_speed(bl)/2;
		ud->steptimer = add_timer(tick+speed, unit_step_timer, bl->id, 0);
	}

	if(ud->state.change_walk_target) {
		if(unit_walktoxy_sub(bl)) {
			return 1;	
		} else {
			clif_fixpos( *bl );
			return 0;
		}
	}

	ud->walkpath.path_pos++;

	if(unit_walktoxy_nextcell(*bl, false, tick)) {
		// Nothing else needs to be done
	} else if(ud->state.running) { // Keep trying to run.
		if (!(unit_run(bl, nullptr, SC_RUN) || unit_run(bl, sd, SC_WUGDASH)) )
			ud->state.running = 0;
	} else {
		if (!ud->stepaction && ud->target_to > 0) {
			// Update target trajectory.
			if(unit_update_chase(*bl, tick, true))
				return 0;
		}

		// Stopped walking. Update to_x and to_y to current location
		ud->to_x = bl->x;
		ud->to_y = bl->y;

		if (bl->type != BL_NPC	// walking npc ignores cell stack limit
			&& !ud->state.ignore_cell_stack_limit
			&& battle_config.official_cell_stack_limit > 0
			&& map_count_oncell(bl->m, x, y, BL_CHAR|BL_NPC, 1) > battle_config.official_cell_stack_limit) {

			//Walked on occupied cell, call unit_walktoxy again
			if(unit_walktoxy(bl, x, y, 8)) {
				//Execute step timer on next step instead
				if (ud->steptimer != INVALID_TIMER) {
					//Execute step timer on next step instead
					delete_timer(ud->steptimer, unit_step_timer);
					ud->steptimer = INVALID_TIMER;
				}
				return 1;
			}
		}
	}

	return 0;
}

/**
 * Delays an xy timer
 * @param tid: Timer ID
 * @param tick: Unused
 * @param id: ID of bl to delay timer on
 * @param data: Data used in timer calls
 * @return 1: Success 0: Fail (No valid bl)
 */
TIMER_FUNC(unit_delay_walktoxy_timer){
	struct block_list *bl = map_id2bl(id);

	if (!bl || bl->prev == nullptr)
		return 0;

	unit_walktoxy(bl, (int16)((data>>16)&0xffff), (int16)(data&0xffff), 0);

	return 1;
}

/**
 * Delays an walk-to-bl timer
 * @param tid: Timer ID
 * @param tick: Unused
 * @param id: ID of bl to delay timer on
 * @param data: Data used in timer calls (target bl)
 * @return 1: Success 0: Fail (No valid bl or target)
 */
TIMER_FUNC(unit_delay_walktobl_timer){
	block_list* bl = map_id2bl( id );
	block_list* tbl = map_id2bl( static_cast<int32>( data ) );

	if(!bl || bl->prev == nullptr || tbl == nullptr)
		return 0;
	else {
		struct unit_data* ud = unit_bl2ud(bl);
		unit_walktobl(bl, tbl, 0, 0);
		ud->target_to = 0;
	}

	return 1;
}

/**
 * Begins the function of walking a unit to an x,y location
 * This is where the path searches and unit can_move checks are done
 * @param bl: Object to send to x,y coordinate
 * @param x: X coordinate where the object will be walking to
 * @param y: Y coordinate where the object will be walking to
 * @param flag: Parameter to decide how to walk
 *	&1: Easy walk (fail if CELL_CHKNOPASS is in direct path)
 *	&2: Force walking (override can_move)
 *	&4: Delay walking for can_move
 *	&8: Search for an unoccupied cell and cancel if none available
 * @return 1: Success 0: Fail or unit_walktoxy_sub()
 */
int32 unit_walktoxy( struct block_list *bl, int16 x, int16 y, unsigned char flag)
{
	nullpo_ret(bl);

	unit_data* ud = unit_bl2ud(bl);

	if (ud == nullptr)
		return 0;

	if ((flag&8) && !map_nearby_freecell(bl->m, x, y, BL_CHAR|BL_NPC, 1)) //This might change x and y
		return 0;

	walkpath_data wpd = { 0 };

	if (!path_search(&wpd, bl->m, bl->x, bl->y, x, y, flag&1, CELL_CHKNOPASS)) // Count walk path cells
		return 0;

	// NPCs do not need to fulfill the following checks
	if( bl->type != BL_NPC ){
		if( wpd.path_len > battle_config.max_walk_path ){
			return 0;
		}

#ifdef OFFICIAL_WALKPATH
		// Official number of walkable cells is 14 if and only if there is an obstacle between.
		if( wpd.path_len > 14 && !path_search_long( nullptr, bl->m, bl->x, bl->y, x, y, CELL_CHKNOPASS ) ){
			return 0;
		}
#endif
	}

	if (flag&4) {
		unit_unattackable(bl);
		unit_stop_attack(bl);

		if(DIFF_TICK(ud->canmove_tick, gettick()) > 0 && DIFF_TICK(ud->canmove_tick, gettick()) < 2000) { // Delay walking command. [Skotlex]
			add_timer(ud->canmove_tick+1, unit_delay_walktoxy_timer, bl->id, (x<<16)|(y&0xFFFF));
			return 1;
		}
	}

	if(!(flag&2) && (!status_bl_has_mode(bl,MD_CANMOVE) || !unit_can_move(bl)))
		return 0;

	ud->state.walk_easy = flag&1;
	ud->to_x = x;
	ud->to_y = y;
	unit_stop_attack(bl); //Sets target to 0

	status_change* sc = status_get_sc(bl);
	if (sc && sc->getSCE(SC_CONFUSION)) // Randomize the target position
		map_random_dir(bl, &ud->to_x, &ud->to_y);

	if(ud->walktimer != INVALID_TIMER) {
		// When you come to the center of the grid because the change of destination while you're walking right now
		// Call a function from a timer unit_walktoxy_sub
		ud->state.change_walk_target = 1;
		return 1;
	}

	TBL_PC *sd = BL_CAST(BL_PC, bl);

	// Start timer to recall summon
	if( sd != nullptr ){
		if (sd->md != nullptr)
			unit_check_start_teleport_timer(&sd->md->bl);
		if (sd->ed != nullptr)
			unit_check_start_teleport_timer(&sd->ed->bl);
		if (sd->hd != nullptr)
			unit_check_start_teleport_timer(&sd->hd->bl);
		if (sd->pd != nullptr)
			unit_check_start_teleport_timer(&sd->pd->bl);
	}

	return unit_walktoxy_sub(bl);
}

/**
 * Timer to walking a unit to another unit's location
 * Calls unit_walktoxy_sub once determined the unit can move
 * @param tid: Object's timer ID
 * @param id: Object's ID
 * @param data: Data passed through timer function (target)
 * @return 0
 */
static TIMER_FUNC(unit_walktobl_sub){
	struct block_list *bl = map_id2bl(id);
	struct unit_data *ud = bl?unit_bl2ud(bl):nullptr;

	if (ud != nullptr && ud->walktimer == INVALID_TIMER && ud->target_to != 0 && ud->target_to == data) {
		if (DIFF_TICK(ud->canmove_tick, tick) > 0) // Keep waiting?
			add_timer(ud->canmove_tick+1, unit_walktobl_sub, id, data);
		else if (unit_can_move(bl))
			unit_walktoxy_sub(bl);
	}

	return 0;
}

/**
 * Tells a unit to walk to a target's location (chase)
 * @param bl: Object that is walking to target
 * @param tbl: Target object
 * @param range: How close to get to target (or attack range if flag&2)
 * @param flag: Extra behaviour
 *	&1: Use easy path seek (obstacles will not be walked around)
 *	&2: Start attacking upon arrival within range, otherwise just walk to target
 * @return 1: Started walking or set timer 0: Failed
 */
int32 unit_walktobl(struct block_list *bl, struct block_list *tbl, int32 range, unsigned char flag)
{
	nullpo_ret(bl);
	nullpo_ret(tbl);

	unit_data *ud  = unit_bl2ud(bl);

	if(ud == nullptr)
		return 0;

	if (!status_bl_has_mode(bl,MD_CANMOVE))
		return 0;

	if (!unit_can_reach_bl(bl, tbl, distance_bl(bl, tbl)+1, flag&1, &ud->to_x, &ud->to_y)) {
		ud->to_x = bl->x;
		ud->to_y = bl->y;
		ud->target_to = 0;

		return 0;
	} else if (range == 0) {
		//Should walk on the same cell as target (for looters)
		ud->to_x = tbl->x;
		ud->to_y = tbl->y;
		//Because of the change of target position the easy walkpath could fail
		//Note: Easy walking is no longer used by default, but we keep this to prevent endless loops [Playtester]
		flag &= ~1;
	}

	ud->state.walk_easy = flag&1;
	ud->target_to = tbl->id;
	ud->chaserange = range; // Note that if flag&2, this SHOULD be attack-range
	ud->state.attack_continue = flag&2?1:0; // Chase to attack.
	unit_stop_attack(bl); //Sets target to 0

	status_change *sc = status_get_sc(bl);
	if (sc && sc->getSCE(SC_CONFUSION)) // Randomize the target position
		map_random_dir(bl, &ud->to_x, &ud->to_y);

	if(ud->walktimer != INVALID_TIMER) {
		ud->state.change_walk_target = 1;

		// New target, make sure a monster is still in chase state
		if (bl->type == BL_MOB && ud->state.attack_continue) {
			mob_data& md = reinterpret_cast<mob_data&>(*bl);
			mob_setstate(md, MSS_RUSH);
		}

		return 1;
	}

	if(DIFF_TICK(ud->canmove_tick, gettick()) > 0) { // Can't move, wait a bit before invoking the movement.
		add_timer(ud->canmove_tick+1, unit_walktobl_sub, bl->id, ud->target_to);
		return 1;
	}

	if(!unit_can_move(bl))
		return 0;

	if (unit_walktoxy_sub(bl))
		return 1;

	return 0;
}

/**
 * Called by unit_run when an object is hit.
 * @param sd Required only when using SC_WUGDASH
 */
void unit_run_hit(struct block_list *bl, status_change *sc, map_session_data *sd, enum sc_type type)
{
	int32 lv = sc->getSCE(type)->val1;

	// If you can't run forward, you must be next to a wall, so bounce back. [Skotlex]
	if (type == SC_RUN)
		clif_status_change(bl, EFST_TING, 1, 0, 0, 0, 0);

	// Set running to 0 beforehand so status_change_end knows not to enable spurt [Kevin]
	unit_bl2ud(bl)->state.running = 0;
	status_change_end(bl, type);

	if (type == SC_RUN) {
		skill_blown(bl, bl, skill_get_blewcount(TK_RUN, lv), unit_getdir(bl), BLOWN_NONE);
		clif_status_change(bl, EFST_TING, 0, 0, 0, 0, 0);
	} else if (sd) {
		clif_fixpos( *bl );
		skill_castend_damage_id(bl, &sd->bl, RA_WUGDASH, lv, gettick(), SD_LEVEL);
	}
	return;
}

/**
 * Set a unit to run, checking for obstacles
 * @param bl: Object that is running
 * @param sd: Required only when using SC_WUGDASH
 * @return true: Success (Finished running) false: Fail (Hit an object/Couldn't run)
 */
bool unit_run(struct block_list *bl, map_session_data *sd, enum sc_type type)
{
	status_change *sc;
	int16 to_x, to_y, dir_x, dir_y;
	int32 i;

	nullpo_retr(false, bl);

	sc = status_get_sc(bl);

	if (!(sc && sc->getSCE(type)))
		return false;

	if (!unit_can_move(bl)) {
		status_change_end(bl, type);
		return false;
	}

	dir_x = dirx[sc->getSCE(type)->val2];
	dir_y = diry[sc->getSCE(type)->val2];

	// Determine destination cell
	to_x = bl->x;
	to_y = bl->y;

	// Search for available path
	for(i = 0; i < AREA_SIZE; i++) {
		if(!map_getcell(bl->m, to_x + dir_x, to_y + dir_y, CELL_CHKPASS))
			break;

		// If sprinting and there's a PC/Mob/NPC, block the path [Kevin]
		if(map_count_oncell(bl->m, to_x + dir_x, to_y + dir_y, BL_PC|BL_MOB|BL_NPC, 0))
			break;

		to_x += dir_x;
		to_y += dir_y;
	}

	// Can't run forward.
	if( (to_x == bl->x && to_y == bl->y) || (to_x == (bl->x + 1) || to_y == (bl->y + 1)) || (to_x == (bl->x - 1) || to_y == (bl->y - 1))) {
		unit_run_hit(bl, sc, sd, type);
		return false;
	}

	if (unit_walktoxy(bl, to_x, to_y, 1))
		return true;

	// There must be an obstacle nearby. Attempt walking one cell at a time.
	do {
		to_x -= dir_x;
		to_y -= dir_y;
	} while (--i > 0 && !unit_walktoxy(bl, to_x, to_y, 1));

	if (i == 0) {
		unit_run_hit(bl, sc, sd, type);
		return false;
	}

	return true;
}

/**
 * Returns duration of an object's current walkpath
 * @param bl: Object that is moving
 * @return Duration of the walkpath
 */
t_tick unit_get_walkpath_time(struct block_list& bl)
{
	t_tick time = 0;
	uint16 speed = status_get_speed(&bl);
	struct unit_data* ud = unit_bl2ud(&bl);

	// The next walk start time is calculated.
	for (uint8 i = 0; i < ud->walkpath.path_len; i++) {
		if (direction_diagonal(ud->walkpath.path[i]))
			time += speed * MOVE_DIAGONAL_COST / MOVE_COST;
		else
			time += speed;
	}

	return time;
}

/**
 * Makes unit attempt to run away from target in a straight line or using hard paths
 * @param bl: Object that is running away from target
 * @param target: Target
 * @param dist: How far bl should run
 * @param flag: unit_walktoxy flag (&1 = straight line escape)
 * @return The duration the unit will run (0 on fail)
 */
t_tick unit_escape(struct block_list *bl, struct block_list *target, int16 dist, uint8 flag)
{
	uint8 dir = map_calc_dir(target, bl->x, bl->y);

	if (flag&1) {
		// Straight line escape
		// Keep moving until we hit an unreachable cell
		for (int16 i = 1; i <= dist; i++) {
			if (map_getcell(bl->m, bl->x + i*dirx[dir], bl->y + i*diry[dir], CELL_CHKNOREACH))
				dist = i - 1;
		}
	} else {
		// Find the furthest reachable cell (then find a walkpath to it)
		while( dist > 0 && map_getcell(bl->m, bl->x + dist*dirx[dir], bl->y + dist*diry[dir], CELL_CHKNOREACH) )
			dist--;
	}

	if (dist > 0 && unit_walktoxy(bl, bl->x + dist * dirx[dir], bl->y + dist * diry[dir], flag))
		return unit_get_walkpath_time(*bl);

	return 0;
}

/**
 * Instant warps a unit to x,y coordinate
 * @param bl: Object to instant warp
 * @param dst_x: X coordinate to warp to
 * @param dst_y: Y coordinate to warp to
 * @param easy: 
 *		0: Hard path check (attempt to go around obstacle)
 *		1: Easy path check (no obstacle on movement path)
 *		2: Long path check (no obstacle on line from start to destination)
 * @param checkpath: Whether or not to do a cell and path check for NOPASS and NOREACH
 * @return True: Success False: Fail
 */
bool unit_movepos(struct block_list *bl, int16 dst_x, int16 dst_y, int32 easy, bool checkpath)
{
	int16 dx,dy;
	struct unit_data        *ud = nullptr;
	map_session_data *sd = nullptr;

	nullpo_retr(false,bl);

	sd = BL_CAST(BL_PC, bl);
	ud = unit_bl2ud(bl);

	if(ud == nullptr)
		return false;

	unit_stop_walking( bl, USW_FIXPOS );
	unit_stop_attack(bl);

	if( checkpath && (map_getcell(bl->m,dst_x,dst_y,CELL_CHKNOPASS) || !path_search(nullptr,bl->m,bl->x,bl->y,dst_x,dst_y,easy,CELL_CHKNOREACH)) )
		return false; // Unreachable

	ud->to_x = dst_x;
	ud->to_y = dst_y;

	unit_setdir(bl, map_calc_dir(bl, dst_x, dst_y), false);

	dx = dst_x - bl->x;
	dy = dst_y - bl->y;

	map_foreachinmovearea(clif_outsight, bl, AREA_SIZE, dx, dy, (sd ? BL_ALL : BL_PC), bl);

	map_moveblock(bl, dst_x, dst_y, gettick());

	ud->walktimer = CLIF_WALK_TIMER; // Arbitrary non-INVALID_TIMER value to make the clif code send walking packets
	map_foreachinmovearea(clif_insight, bl, AREA_SIZE, -dx, -dy, (sd ? BL_ALL : BL_PC), bl);
	ud->walktimer = INVALID_TIMER;

	if(sd) {
		if( !sd->npc_ontouch_.empty() )
			npc_touchnext_areanpc(sd,false);

		if(map_getcell(bl->m,bl->x,bl->y,CELL_CHKNPC)) {
			npc_touch_area_allnpc(sd, bl->m, bl->x, bl->y);

			if (bl->prev == nullptr) // Script could have warped char, abort remaining of the function.
				return false;
		} else
			sd->areanpc.clear();

		if( sd->status.pet_id > 0 && sd->pd && sd->pd->pet.intimate > PET_INTIMATE_NONE ) {
			// Check if pet needs to be teleported. [Skotlex]
			int32 flag = 0;
			struct block_list* pbl = &sd->pd->bl;

			if( !checkpath && !path_search(nullptr,pbl->m,pbl->x,pbl->y,dst_x,dst_y,0,CELL_CHKNOPASS) )
				flag = 1;
			else if (!check_distance_bl(&sd->bl, pbl, AREA_SIZE)) // Too far, teleport.
				flag = 2;

			if( flag ) {
				unit_movepos(pbl,sd->bl.x,sd->bl.y, 0, 0);
				clif_slide(*pbl,pbl->x,pbl->y);
			}
		}
	}

	return true;
}

/**
 * Sets direction of a unit
 * @param bl: Object to set direction
 * @param dir: Direction (0-7)
 * @param send_update: Update the client area of direction (default: true)
 * @return True on success or False on failure
 */
bool unit_setdir(block_list *bl, uint8 dir, bool send_update)
{
	nullpo_ret(bl);

	unit_data *ud = unit_bl2ud(bl);

	if (ud == nullptr)
		return false;

	ud->dir = dir;

	if (bl->type == BL_PC) {
		map_session_data *sd = BL_CAST(BL_PC, bl);

		sd->head_dir = DIR_NORTH;
		sd->status.body_direction = ud->dir;
	}

	if (send_update)
		clif_changed_dir(*bl, AREA);

	return true;
}

/**
 * Gets direction of a unit
 * @param bl: Object to get direction
 * @return direction (0-7)
 */
uint8 unit_getdir(struct block_list *bl)
{
	struct unit_data *ud;

	nullpo_ret(bl);

	ud = unit_bl2ud(bl);

	if (!ud)
		return 0;

	return ud->dir;
}

/**
 * Pushes a unit in a direction by a given amount of cells
 * There is no path check, only map cell restrictions are respected
 * @param bl: Object to push
 * @param dx: Destination cell X
 * @param dy: Destination cell Y
 * @param count: How many cells to push bl
 * @param flag: See skill.hpp::e_skill_blown
 * @return count (can be modified due to map cell restrictions)
 */
int32 unit_blown(struct block_list* bl, int32 dx, int32 dy, int32 count, enum e_skill_blown flag)
{
	if(count) {
		map_session_data* sd;
		struct skill_unit* su = nullptr;
		int32 nx, ny, result;

		sd = BL_CAST(BL_PC, bl);
		su = BL_CAST(BL_SKILL, bl);

		result = path_blownpos(bl->m, bl->x, bl->y, dx, dy, count);

		nx = result>>16;
		ny = result&0xffff;

		if(!su)
			unit_stop_walking( bl, USW_NONE );

		if( sd ) {
			unit_stop_stepaction(bl); //Stop stepaction when knocked back
			sd->ud.to_x = nx;
			sd->ud.to_y = ny;
		}

		dx = nx-bl->x;
		dy = ny-bl->y;

		if(dx || dy) {
			map_foreachinmovearea(clif_outsight, bl, AREA_SIZE, dx, dy, bl->type == BL_PC ? BL_ALL : BL_PC, bl);

			if(su) {
				if (su->group && skill_get_unit_flag(su->group->skill_id, UF_KNOCKBACKGROUP))
					skill_unit_move_unit_group(su->group, bl->m, dx, dy);
				else
					skill_unit_move_unit(bl, nx, ny);
			} else
				map_moveblock(bl, nx, ny, gettick());

			map_foreachinmovearea(clif_insight, bl, AREA_SIZE, -dx, -dy, bl->type == BL_PC ? BL_ALL : BL_PC, bl);

			if(!(flag&BLOWN_DONT_SEND_PACKET))
				clif_blown(bl);

			if(sd) {
				if(!sd->npc_ontouch_.empty())
					npc_touchnext_areanpc(sd, false);

				if(map_getcell(bl->m, bl->x, bl->y, CELL_CHKNPC))
					npc_touch_area_allnpc(sd, bl->m, bl->x, bl->y);
				else
					sd->areanpc.clear();
			}
		}

		count = distance(dx, dy);
	}

	return count;  // Return amount of knocked back cells
}

/**
 * Checks if unit can be knocked back / stopped by skills.
 * @param bl: Object to check
 * @param flag
 *		0x1 - Offensive (not set: self skill, e.g. Backslide)
 *		0x2 - Knockback type (not set: Stop type, e.g. Ankle Snare)
 *		0x4 - Boss attack
 *		0x8 - Ignore target player 'special_state.no_knockback'
 * @return reason for immunity
 *		UB_KNOCKABLE - can be knocked back / stopped
 *		UB_NO_KNOCKBACK_MAP - at WOE/BG map
 *		UB_MD_KNOCKBACK_IMMUNE - target is MD_KNOCKBACK_IMMUNE
 *		UB_TARGET_BASILICA - target is in Basilica area (Pre-Renewal)
 *		UB_TARGET_NO_KNOCKBACK - target has 'special_state.no_knockback'
 *		UB_TARGET_TRAP - target is trap that cannot be knocked back
 */
enum e_unit_blown unit_blown_immune(struct block_list* bl, uint8 flag)
{
	if ((flag&0x1)
		&& (map_flag_gvg2(bl->m) || map_getmapflag(bl->m, MF_BATTLEGROUND))
		&& ((flag&0x2) || !(battle_config.skill_trap_type&0x1)))
		return UB_NO_KNOCKBACK_MAP; // No knocking back in WoE / BG

	switch (bl->type) {
		case BL_MOB:
			// Immune can't be knocked back
			if (((flag&0x1) && status_bl_has_mode(bl,MD_KNOCKBACKIMMUNE))
				&& ((flag&0x2) || !(battle_config.skill_trap_type&0x2)))
				return UB_MD_KNOCKBACK_IMMUNE;
			break;
		case BL_PC: {
				map_session_data *sd = BL_CAST(BL_PC, bl);

#ifndef RENEWAL
				// Basilica caster can't be knocked-back by normal monsters.
				if( !(flag&0x4) && sd->sc.getSCE(SC_BASILICA) && sd->sc.getSCE(SC_BASILICA)->val4 == sd->bl.id)
					return UB_TARGET_BASILICA;
#endif
				// Target has special_state.no_knockback (equip)
				if( (flag&(0x1|0x2)) && !(flag&0x8) && sd->special_state.no_knockback )
					return UB_TARGET_NO_KNOCKBACK;
			}
			break;
		case BL_SKILL: {
				struct skill_unit* su = (struct skill_unit *)bl;
				// Trap cannot be knocked back
				if (su && su->group && skill_get_unit_flag(su->group->skill_id, UF_NOKNOCKBACK))
					return UB_TARGET_TRAP;
			}
			break;
	}

	//Object can be knocked back / stopped
	return UB_KNOCKABLE;
}

/**
 * Warps a unit to a map/position
 * pc_setpos is used for player warping
 * This function checks for "no warp" map flags, so it's safe to call without doing nowarpto/nowarp checks
 * @param bl: Object to warp
 * @param m: Map ID from bl structure (NOT index)
 * @param x: Destination cell X
 * @param y: Destination cell Y
 * @param type: Clear type used in clif_clearunit_area()
 * @return Success(0); Failed(1); Error(2); unit_remove_map() Failed(3); map_addblock Failed(4)
 */
int32 unit_warp(struct block_list *bl,int16 m,int16 x,int16 y,clr_type type)
{
	struct unit_data *ud;

	nullpo_ret(bl);

	ud = unit_bl2ud(bl);

	if(bl->prev==nullptr || !ud)
		return 1;

	if (type == CLR_DEAD)
		// Type 1 is invalid, since you shouldn't warp a bl with the "death"
		// animation, it messes up with unit_remove_map! [Skotlex]
		return 1;

	if( m < 0 )
		m = bl->m;

	switch (bl->type) {
		case BL_MOB:
			if (map_getmapflag(bl->m, MF_MONSTER_NOTELEPORT) && ((TBL_MOB*)bl)->master_id == 0)
				return 1;

			if (m != bl->m && map_getmapflag(m, MF_NOBRANCH) && battle_config.mob_warp&4 && !(((TBL_MOB *)bl)->master_id))
				return 1;
			break;
		case BL_PC:
			if (map_getmapflag(bl->m, MF_NOTELEPORT))
				return 1;
			break;
	}

	if (x < 0 || y < 0) { // Random map position.
		if (!map_search_freecell(nullptr, m, &x, &y, -1, -1, 1)) {
			ShowWarning("unit_warp failed. Unit Id:%d/Type:%d, target position map %d (%s) at [%d,%d]\n", bl->id, bl->type, m, map[m].name, x, y);
			return 2;

		}
	} else if ( bl->type != BL_NPC && map_getcell(m,x,y,CELL_CHKNOREACH)) { // Invalid target cell
		ShowWarning("unit_warp: Specified non-walkable target cell: %d (%s) at [%d,%d]\n", m, map[m].name, x,y);

		if (!map_search_freecell(nullptr, m, &x, &y, 4, 4, 1)) { // Can't find a nearby cell
			ShowWarning("unit_warp failed. Unit Id:%d/Type:%d, target position map %d (%s) at [%d,%d]\n", bl->id, bl->type, m, map[m].name, x, y);
			return 2;
		}
	}

	if (bl->type == BL_PC) // Use pc_setpos
		return pc_setpos((TBL_PC*)bl, map_id2index(m), x, y, type);

	if (!unit_remove_map(bl, type))
		return 3;

	if (bl->m != m && battle_config.clear_unit_onwarp &&
		battle_config.clear_unit_onwarp&bl->type)
		skill_clear_unitgroup(bl);

	bl->x = ud->to_x = x;
	bl->y = ud->to_y = y;
	bl->m = m;

	switch (bl->type) {
		case BL_NPC:
		{
			TBL_NPC* nd = reinterpret_cast<npc_data*>(bl);
			map_addnpc(m, nd);
			npc_setcells(nd);
			break;
		}
		case BL_MOB:
		{
			TBL_MOB* md = reinterpret_cast<mob_data*>(bl);
			// If slaves are set to stick with their master they should drop target if recalled at range
			if (battle_config.slave_stick_with_master && md->target_id != 0) {
				block_list* tbl = map_id2bl(md->target_id);
				if (tbl == nullptr || !check_distance_bl(bl, tbl, AREA_SIZE)) {
					md->target_id = 0;
				}
			}
			break;
		}
	}

	if(map_addblock(bl))
		return 4; //error on adding bl to map

	clif_spawn(bl);
	skill_unit_move(bl,gettick(),1);

	if (!battle_config.slave_stick_with_master && bl->type == BL_MOB && mob_countslave(bl) > 0)
		mob_warpslave(bl,MOB_SLAVEDISTANCE);

	return 0;
}

/**
 * Calculates the exact coordinates of a bl considering the walktimer
 * This is needed because we only update X/Y when finishing movement to the next cell
 * Officially, however, the coordinates update when crossing the border to the next cell
 * The coordinates are stored in unit_data.pos together with the tick based on which they were calculated
 * Access to these coordinates is only allowed through corresponding unit_data class functions
 * This function makes sure calculation only happens when it's needed to save performance
 * @param tick: Tick based on which we calculate the coordinates
 */
void unit_data::update_pos(t_tick tick)
{
	// Check if coordinates are still up-to-date
	if (DIFF_TICK(tick, this->pos.tick) < MIN_POS_INTERVAL)
		return;

	if (this->bl == nullptr)
		return;

	// Set initial coordinates
	this->pos.x = this->bl->x;
	this->pos.y = this->bl->y;
	this->pos.sx = 8;
	this->pos.sy = 8;

	// Remember time at which we did the last calculation
	this->pos.tick = tick;

	if (this->walkpath.path_pos >= this->walkpath.path_len)
		return;

	if (this->walktimer == INVALID_TIMER)
		return;

	const TimerData* td = get_timer(this->walktimer);

	if (td == nullptr)
		return;

	// Get how much percent we traversed on the timer
	double cell_percent = 1.0 - ((double)DIFF_TICK(td->tick, tick) / (double)td->data);

	if (cell_percent > 0.0 && cell_percent < 1.0) {
		// Set subcell coordinates according to timer
		// This gives a value between 8 and 39
		this->pos.sx = static_cast<uint8>(24.0 + dirx[this->walkpath.path[this->walkpath.path_pos]] * 16.0 * cell_percent);
		this->pos.sy = static_cast<uint8>(24.0 + diry[this->walkpath.path[this->walkpath.path_pos]] * 16.0 * cell_percent);
		// 16-31 reflect sub position 0-15 on the current cell
		// 8-15 reflect sub position 8-15 at -1 main coordinate
		// 32-39 reflect sub position 0-7 at +1 main coordinate
		if (this->pos.sx < 16 || this->pos.sy < 16 || this->pos.sx > 31 || this->pos.sy > 31) {
			if (this->pos.sx < 16) this->pos.x--;
			if (this->pos.sy < 16) this->pos.y--;
			if (this->pos.sx > 31) this->pos.x++;
			if (this->pos.sy > 31) this->pos.y++;
		}
		this->pos.sx %= 16;
		this->pos.sy %= 16;
	}
	else if (cell_percent >= 1.0) {
		// Assume exactly one cell moved
		this->pos.x += dirx[this->walkpath.path[this->walkpath.path_pos]];
		this->pos.y += diry[this->walkpath.path[this->walkpath.path_pos]];
	}
}

/**
 * Helper function to get the exact X coordinate
 * This ensures that the coordinate is calculated when needed
 * @param tick: Tick based on which we calculate the coordinate
 * @return The exact X coordinate
 */
int16 unit_data::getx(t_tick tick) {
	// Make sure exact coordinates are up-to-date
	this->update_pos(tick);
	return this->pos.x;
}

/**
 * Helper function to get the exact Y coordinate
 * This ensures that the coordinate is calculated when needed
 * @param tick: Tick based on which we calculate the coordinate
 * @return The exact Y coordinate
 */
int16 unit_data::gety(t_tick tick) {
	// Make sure exact coordinates are up-to-date
	this->update_pos(tick);
	return this->pos.y;
}

/**
 * Helper function to get exact coordinates
 * This ensures that the coordinates are calculated when needed
 * @param x: Will be set to the exact X value of the bl
 * @param y: Will be set to the exact Y value of the bl
 * @param sx: Will be set to the exact subcell X value of the bl
 * @param sy: Will be set to the exact subcell Y value of the bl
 * @param tick: Tick based on which we calculate the coordinate
 * @return The exact Y coordinate
 */
void unit_data::getpos(int16 &x, int16 &y, uint8 &sx, uint8 &sy, t_tick tick) {
	// Make sure exact coordinates are up-to-date
	this->update_pos(tick);
	x = this->pos.x;
	y = this->pos.y;
	sx = this->pos.sx;
	sy = this->pos.sy;
}

/**
 * Updates the walkpath of a unit to end after 0.5-1.5 cells moved
 * Sends required packet for proper display on the client using subcoordinates
 * @param bl: Object to stop walking
 */
void unit_stop_walking_soon(struct block_list& bl, t_tick tick)
{
	struct unit_data* ud = unit_bl2ud(&bl);

	if (ud == nullptr)
		return;

	int16 ox = bl.x, oy = bl.y; // Remember original x and y coordinates
	int16 path_remain = 1; // Remaining path to walk
	bool shortened = false;

	if (ud->walkpath.path_pos + 1 >= ud->walkpath.path_len) {
		// Less than 1 cell left to walk so no need to shorten the path
		// Since we don't need to resend the move packet, we don't need to calculate the exact coordinates
		path_remain = ud->walkpath.path_len - ud->walkpath.path_pos;
	}
	else {
		// Set coordinates to exact coordinates
		ud->getpos(bl.x, bl.y, ud->sx, ud->sy, tick);

		// If x or y already changed, we need to move one more cell
		if (ox != bl.x || oy != bl.y)
			path_remain = 2;

		// Shorten walkpath
		if (ud->walkpath.path_pos + path_remain < ud->walkpath.path_len) {
			ud->walkpath.path_len = ud->walkpath.path_pos + path_remain;
			shortened = true;
		}
	}

	// Make sure to_x and to_y match the walk path even if not shortened in case they were modified
	ud->to_x = ox;
	ud->to_y = oy;
	for (int32 i = 0; i < path_remain; i++) {
		ud->to_x += dirx[ud->walkpath.path[ud->walkpath.path_pos + i]];
		ud->to_y += diry[ud->walkpath.path[ud->walkpath.path_pos + i]];
	}
	// To prevent sending a pointless walk command
	ud->state.change_walk_target = 0;

	// Send movement packet with calculated coordinates and subcoordinates
	// Only need to send if walkpath was shortened
	if (shortened)
		clif_move(*ud);

	// Reset coordinates
	bl.x = ox;
	bl.y = oy;
	ud->sx = 8;
	ud->sy = 8;
}

/**
 * Stops a unit from walking
 * @param bl: Object to stop walking
 * @param type: Options, see e_unit_stop_walking
 * @return Success(true); Failed(false);
 */
bool unit_stop_walking( block_list* bl, int32 type, t_tick canmove_delay ){
	struct unit_data *ud;
	const struct TimerData* td = nullptr;
	t_tick tick;

	if( bl == nullptr ){
		return false;
	}

	ud = unit_bl2ud(bl);

	if(!ud || (!(type&USW_FORCE_STOP) && ud->walktimer == INVALID_TIMER))
		return false;

	// NOTE: We are using timer data after deleting it because we know the
	// delete_timer function does not mess with it. If the function's
	// behaviour changes in the future, this code could break!
	if (ud->walktimer != INVALID_TIMER) {
		td = get_timer(ud->walktimer);
		delete_timer(ud->walktimer, unit_walktoxy_timer);
		ud->walktimer = INVALID_TIMER;
	}
	ud->state.change_walk_target = 0;
	tick = gettick();

	if( (type&USW_MOVE_ONCE && !ud->walkpath.path_pos) // Force moving at least one cell.
	||  (type&USW_MOVE_FULL_CELL && td && DIFF_TICK(td->tick, tick) <= td->data/2) // Enough time has passed to cover half-cell
	) {
		ud->walkpath.path_len = ud->walkpath.path_pos+1;
		unit_walktoxy_timer(INVALID_TIMER, tick, bl->id, ud->walkpath.path_pos);
	}

	if (type&USW_FIXPOS) {
		// Stop on cell center
		ud->sx = 8;
		ud->sy = 8;
		clif_fixpos(*bl);
	}

	ud->walkpath.path_len = 0;
	ud->walkpath.path_pos = 0;
	ud->to_x = bl->x;
	ud->to_y = bl->y;

	if (type&USW_RELEASE_TARGET)
		ud->target_to = 0;

	if( canmove_delay > 0 ){
		ud->canmove_tick = gettick() + canmove_delay;
	}

	// Re-added, the check in unit_set_walkdelay means dmg during running won't fall through to this place in code [Kevin]
	if (ud->state.running) {
		status_change_end(bl, SC_RUN);
		status_change_end(bl, SC_WUGDASH);
	}

	return true;
}

/**
 * Initiates a skill use by a unit
 * @param src: Source object initiating skill use
 * @param target_id: Target ID (bl->id)
 * @param skill_id: Skill ID
 * @param skill_lv: Skill Level
 * @return unit_skilluse_id2()
 */
int32 unit_skilluse_id(struct block_list *src, int32 target_id, uint16 skill_id, uint16 skill_lv)
{
	return unit_skilluse_id2(
		src, target_id, skill_id, skill_lv,
		skill_castfix(src, skill_id, skill_lv),
		skill_get_castcancel(skill_id)
	);
}

/**
 * Checks if a unit is walking
 * @param bl: Object to check walk status
 * @return Walking(1); Not Walking(0)
 */
int32 unit_is_walking(struct block_list *bl)
{
	struct unit_data *ud = unit_bl2ud(bl);

	nullpo_ret(bl);

	if(!ud)
		return 0;

	return (ud->walktimer != INVALID_TIMER);
}

/** 
 * Checks if a unit is able to move based on status changes
 * View the StatusChangeStateTable in status.cpp for a list of statuses
 * Some statuses are still checked here due too specific variables
 * @author [Skotlex]
 * @param bl: Object to check
 * @return True - can move; False - can't move
 */
bool unit_can_move(struct block_list *bl) {
	map_session_data *sd;
	struct unit_data *ud;
	status_change *sc;

	nullpo_ret(bl);

	ud = unit_bl2ud(bl);
	sc = status_get_sc(bl);
	sd = BL_CAST(BL_PC, bl);

	if (!ud)
		return false;

	if (ud->skilltimer != INVALID_TIMER && ud->skill_id != LG_EXEEDBREAK && (!sd || !pc_checkskill(sd, SA_FREECAST) || skill_get_inf2(ud->skill_id, INF2_ISGUILD)))
		return false; // Prevent moving while casting

	if (DIFF_TICK(ud->canmove_tick, gettick()) > 0)
		return false;

	if ((sd && (pc_issit(sd) || sd->state.vending || sd->state.buyingstore || (sd->state.block_action & PCBLOCK_MOVE) || sd->state.mail_writing)) || ud->state.blockedmove)
		return false; // Can't move

	// Status changes that block movement
	if (sc && sc->cant.move)
		return false;

	// Icewall walk block special trapped monster mode
	if(bl->type == BL_MOB) {
		struct mob_data *md = BL_CAST(BL_MOB, bl);
		if(md && ((status_has_mode(&md->status,MD_STATUSIMMUNE) && battle_config.boss_icewall_walk_block == 1 && map_getcell(bl->m,bl->x,bl->y,CELL_CHKICEWALL))
			|| (!status_has_mode(&md->status,MD_STATUSIMMUNE) && battle_config.mob_icewall_walk_block == 1 && map_getcell(bl->m,bl->x,bl->y,CELL_CHKICEWALL)))) {
			md->walktoxy_fail_count = 1; //Make sure rudeattacked skills are invoked
			return false;
		}
	}

	return true;
}

/**
 * Resumes running (RA_WUGDASH or TK_RUN) after a walk delay
 * @param tid: Timer ID
 * @param id: Object ID
 * @param data: Data passed through timer function (unit_data)
 * @return 0
 */
TIMER_FUNC(unit_resume_running){
	struct unit_data *ud = (struct unit_data *)data;
	TBL_PC *sd = map_id2sd(id);

	if (sd && pc_isridingwug(sd))
		clif_skill_nodamage(ud->bl,*ud->bl,RA_WUGDASH,ud->skill_lv,sc_start4(ud->bl,ud->bl,SC_WUGDASH,100,ud->skill_lv,unit_getdir(ud->bl),0,0,0));
	else
		clif_skill_nodamage(ud->bl,*ud->bl,TK_RUN,ud->skill_lv,sc_start4(ud->bl,ud->bl,SC_RUN,100,ud->skill_lv,unit_getdir(ud->bl),0,0,0));

	if (sd)
		clif_walkok(*sd);

	return 0;
}

/**
 * Sets the delays that prevent attacks and skill usage considering the bl type
 * Makes sure that delays are not decreased in case they are already higher
 * Will also invoke bl type specific delay functions when required
 * @param bl Object to apply attack delay to
 * @param tick Current tick
 * @param event The event that resulted in calling this function
 */
void unit_set_attackdelay(block_list& bl, t_tick tick, e_delay_event event)
{
	unit_data* ud = unit_bl2ud(&bl);

	if (ud == nullptr)
		return;

	t_tick attack_delay = 0;
	t_tick act_delay = 0;

	switch (bl.type) {
		case BL_PC:
			switch (event) {
				case DELAY_EVENT_CASTBEGIN_ID:
				case DELAY_EVENT_CASTBEGIN_POS:
					if (reinterpret_cast<map_session_data*>(&bl)->skillitem == ud->skill_id) {
						// Skills used from items don't seem to give any attack or act delay
						return;
					}
					[[fallthrough]];
				case DELAY_EVENT_ATTACK:
				case DELAY_EVENT_PARRY:
					// Officially for players it just remembers the last attack time here and applies the delays during the comparison
					// But we pre-calculate the delays instead and store them in attackabletime and canact_tick
					attack_delay = status_get_adelay(&bl);
					// A fixed delay is added here which is equal to the minimum attack motion you can get
					// This ensures that at max ASPD attackabletime and canact_tick are equal
					act_delay = status_get_amotion(&bl) + (pc_maxaspd(reinterpret_cast<map_session_data*>(&bl)) / AMOTION_DIVIDER_PC);
					break;
			}
			break;
		case BL_MOB:
			switch (event) {
				case DELAY_EVENT_ATTACK:
				case DELAY_EVENT_CASTEND:
				case DELAY_EVENT_CASTCANCEL:
					// This represents setting of attack delay (recharge time) that happens for non-PCs
					attack_delay = status_get_adelay(&bl);
					break;
				case DELAY_EVENT_CASTBEGIN_ID:
				case DELAY_EVENT_CASTBEGIN_POS:
					// When monsters use skills, they only get delays on cast end and cast cancel
					break;
			}
			// Set monster-specific delays (inactive AI time, monster skill delays)
			mob_set_delay(reinterpret_cast<mob_data&>(bl), tick, event);
			break;
		case BL_HOM:
			switch (event) {
				case DELAY_EVENT_ATTACK:
					// This represents setting of attack delay (recharge time) that happens for non-PCs
					attack_delay = status_get_adelay(&bl);
					break;
				case DELAY_EVENT_CASTBEGIN_ID:
				case DELAY_EVENT_CASTBEGIN_POS:
					// For non-PCs that can be controlled from the client, there is a security delay of 200ms
					// However to prevent tricks to use skills faster, we have a config to use amotion instead
					if (battle_config.amotion_min_skill_delay == 1)
						act_delay = status_get_amotion(&bl) + MAX_ASPD_NOPC;
					else
						act_delay = MIN_DELAY_SLAVE;
					break;
			}
			break;
		case BL_MER:
			switch (event) {
				case DELAY_EVENT_ATTACK:
					// This represents setting of attack delay (recharge time) that happens for non-PCs
					attack_delay = status_get_adelay(&bl);
					break;
				case DELAY_EVENT_CASTBEGIN_ID:
					// For non-PCs that can be controlled from the client, there is a security delay of 200ms
					// However to prevent tricks to use skills faster, we have a config to use amotion instead
					if (battle_config.amotion_min_skill_delay == 1)
						act_delay = status_get_amotion(&bl) + MAX_ASPD_NOPC;
					else
						act_delay = MIN_DELAY_SLAVE;
					break;
				case DELAY_EVENT_CASTBEGIN_POS:
					// For ground skills, mercenaries work similar to players
					attack_delay = status_get_adelay(&bl);
					act_delay = status_get_amotion(&bl) + MAX_ASPD_NOPC;
					break;
			}
			break;
		default:
			// Fallback to original behavior as unit type is not fully integrated yet
			switch (event) {
				case DELAY_EVENT_ATTACK:
					attack_delay = status_get_adelay(&bl);
					break;
				case DELAY_EVENT_CASTBEGIN_ID:
				case DELAY_EVENT_CASTBEGIN_POS:
					act_delay = status_get_amotion(&bl);
					break;
			}
			break;
	}

	// When setting delays, we need to make sure not to decrease them in case they've been set by another source already
	if (attack_delay > 0)
		ud->attackabletime = i64max(tick + attack_delay, ud->attackabletime);
	if (act_delay > 0)
		ud->canact_tick = i64max(tick + act_delay, ud->canact_tick);
}

/**
 * Updates skill delays according to cast time and minimum delay, and applies security casttime
 * @param bl Object to apply update delay for
 * @param tick Current tick
 * @param event The event that resulted in calling this function
 */
void unit_set_castdelay(unit_data& ud, t_tick tick, int32 casttime) {
	// Use casttime or minimum delay, whatever is longer
	t_tick cast_delay = i64max(casttime, battle_config.min_skill_delay_limit);

	// Only apply the cast delay, if it is longer than the act delay (set by unit_set_attackdelay)
	ud.canact_tick = i64max(ud.canact_tick, tick + cast_delay);

	// Security delay that will be removed at castend again
	ud.canact_tick += SECURITY_CASTTIME;
}

/**
 * Applies a walk delay to a unit
 * @param bl: Object to apply walk delay to
 * @param tick: Current tick
 * @param delay: Amount of time to set walk delay
 * @param type: Type of delay
 *	0: Damage induced delay; Do not change previous delay
 *	1: Skill induced delay; Walk delay can only be increased, not decreased
 * @param skill_id: ID of skill that dealt damage (type 0 only)
 * @return Success(1); Fail(0);
 */
int32 unit_set_walkdelay(struct block_list *bl, t_tick tick, t_tick delay, int32 type, uint16 skill_id)
{
	struct unit_data *ud = unit_bl2ud(bl);

	if (delay <= 0 || !ud)
		return 0;

	if (type) {
		//Bosses can ignore skill induced walkdelay (but not damage induced)
		if(bl->type == BL_MOB && status_has_mode(status_get_status_data(*bl),MD_STATUSIMMUNE))
			return 0;
		//Make sure walk delay is not decreased
		if (DIFF_TICK(ud->canmove_tick, tick+delay) > 0)
			return 0;
	} else {
		if (bl->type == BL_MOB) {
			mob_data& md = *reinterpret_cast<mob_data*>(bl);

			// Mob needs to escape, don't stop it
			if (md.state.can_escape == 1)
				return 0;
		}
		// Trapped or legacy walk delay system disabled
		if (!unit_can_move(bl) || !(bl->type&battle_config.damage_walk_delay)) {
			// Stop on the closest cell center
			unit_stop_walking( bl, USW_MOVE_FULL_CELL );
			return 0;
		}

		switch (skill_id) {
			case MG_FIREWALL:
			case PR_SANCTUARY:
			case NJ_KAENSIN:
				// When using legacy walk delay, these skills should just stop the target
				delay = 1;
				break;
		}

		//Immune to being stopped for double the flinch time
		if (DIFF_TICK(ud->canmove_tick, tick-delay) > 0)
			return 0;
	}

	ud->canmove_tick = tick + delay;

	if (ud->walktimer != INVALID_TIMER) { // Stop walking, if chasing, readjust timers.
		if (delay == 1) // Minimal delay (walk-delay) disabled. Just stop walking.
			unit_stop_walking( bl, USW_NONE );
		else {
			// Resume running after can move again [Kevin]
			if(ud->state.running)
				add_timer(ud->canmove_tick, unit_resume_running, bl->id, (intptr_t)ud);
			else {
				unit_stop_walking( bl, USW_MOVE_FULL_CELL );

				if(ud->target_to != 0)
					add_timer(ud->canmove_tick+1, unit_walktobl_sub, bl->id, ud->target_to);
			}
		}
	}

	return 1;
}
//==========================================
// [keitenai] Delay System
//==========================================
bool k_tick_check(class map_session_data *sd, t_tick k_tick_t, int k_tick_c, int kdelay_n, int kdelay_w) {
	char msg[200];
	int m_castle = 0;

	if (map_getmapflag(sd->bl.m, MF_GVG_CASTLE) || map_getmapflag(sd->bl.m, MF_GVG_TE_CASTLE)){
		m_castle = 1;
		sd->kdelay = kdelay_w;
	}
	else
		sd->kdelay = kdelay_n;

	if (DIFF_TICK(k_tick_t, gettick()) > 0) {
		if (battle_config.KEITENAI_SHOW_DELAY) {
			sprintf(msg,"[%I64i] second(s) skill use delay", (k_tick_t - gettick()) / 1000);
			clif_messagecolor(&sd->bl, color_table[COLOR_RED], msg, false, SELF);
		}
		if ((m_castle && (k_tick_c > (kdelay_w / Acceptable_Packet))) || k_tick_c > (kdelay_n / Acceptable_Packet))
			clif_authfail_fd(sd->fd, 9); // Disconnect Player

		sd->k_tick_c = k_tick_c + 1;
		return true;
	}
	return false;
}

/**
 * Performs checks for a unit using a skill and executes after cast time completion
 * @param src: Object using skill
 * @param target_id: Target ID (bl->id)
 * @param skill_id: Skill ID
 * @param skill_lv: Skill Level
 * @param casttime: Initial cast time before cast time reductions
 * @param castcancel: Whether or not the skill can be cancelled by interruption (hit)
 * @return Success(1); Fail(0);
 */
int32 unit_skilluse_id2(struct block_list *src, int32 target_id, uint16 skill_id, uint16 skill_lv, int32 casttime, int32 castcancel, bool ignore_range)
{
	struct unit_data *ud;
	status_change *sc;
	map_session_data *sd = nullptr;
	struct block_list * target = nullptr;
	t_tick tick = gettick();
	int32 combo = 0, range;

	nullpo_ret(src);

	if(status_isdead(*src))
		return 0; // Do not continue source is dead

	sd = BL_CAST(BL_PC, src);
	ud = unit_bl2ud(src);

	if(ud == nullptr)
		return 0;

	if (ud && ud->state.blockedskill)
		return 0;

	sc = status_get_sc(src);

	if (sc != nullptr && sc->empty())
		sc = nullptr; // Unneeded

	int32 inf = skill_get_inf(skill_id);
	std::shared_ptr<s_skill_db> skill = skill_db.find(skill_id);

	if (!skill)
		return 0;

	// temp: used to signal combo-skills right now.
	if (sc && sc->getSCE(SC_COMBO) &&
		skill_is_combo(skill_id) &&
		(sc->getSCE(SC_COMBO)->val1 == skill_id ||
		(sd?skill_check_condition_castbegin(*sd,skill_id,skill_lv):0) )) {
		if (skill_is_combo(skill_id) == 2 && target_id == src->id && ud->target > 0)
			target_id = ud->target;
		else if (sc->getSCE(SC_COMBO)->val2)
			target_id = sc->getSCE(SC_COMBO)->val2;
		else if (target_id == src->id || ud->target > 0)
			target_id = ud->target;

		if (inf&INF_SELF_SKILL && skill->nk[NK_NODAMAGE])// exploit fix
			target_id = src->id;

		combo = 1;
	} else if (target_id == src->id && inf&INF_SELF_SKILL && skill->inf2[INF2_NOTARGETSELF]) {
		target_id = ud->target; // Auto-select target. [Skotlex]
		combo = 1;
	}

	if (sd) {
		// Target_id checking.
		if(skill_isNotOk(skill_id, *sd))
			return 0;

		switch(skill_id) { // Check for skills that auto-select target
			case MO_CHAINCOMBO:
				if (sc && sc->getSCE(SC_BLADESTOP)) {
					if ((target=map_id2bl(sc->getSCE(SC_BLADESTOP)->val4)) == nullptr)
						return 0;
				}
				break;
			case GC_WEAPONCRUSH:
				if (sc && sc->getSCE(SC_WEAPONBLOCK_ON)) {
					if ((target = map_id2bl(sc->getSCE(SC_WEAPONBLOCK_ON)->val1)) == nullptr)
						return 0;
					combo = 1;
				}
				break;
			case RL_QD_SHOT:
				if (sc && sc->getSCE(SC_QD_SHOT_READY)) {
					if ((target = map_id2bl(sc->getSCE(SC_QD_SHOT_READY)->val1)) == nullptr)
						return 0;
					combo = 1;
				}
				break;
			case WE_MALE:
			case WE_FEMALE:
				if (!sd->status.partner_id)
					return 0;

				target = (struct block_list*)map_charid2sd(sd->status.partner_id);

				if (!target) {
					clif_skill_fail( *sd, skill_id );
					return 0;
				}
				break;
		}

		if (target)
			target_id = target->id;
	} else if (src->type == BL_HOM) {
		switch(skill_id) { // Homun-auto-target skills.
			case HLIF_HEAL:
			case HLIF_AVOID:
			case HAMI_DEFENCE:
			case HAMI_CASTLE:
				target = battle_get_master(src);

				if (!target)
					return 0;

				target_id = target->id;
				break;
			case MH_SONIC_CRAW:
			case MH_TINDER_BREAKER: {
				int32 skill_id2 = ((skill_id==MH_SONIC_CRAW)?MH_MIDNIGHT_FRENZY:MH_EQC);

				if(sc->getSCE(SC_COMBO) && sc->getSCE(SC_COMBO)->val1 == skill_id2) { // It's a combo
					target_id = sc->getSCE(SC_COMBO)->val2;
					combo = 1;
					casttime = -1;
				}
				break;
			}
		}
	}

	if( !target ) // Choose default target
		target = map_id2bl(target_id);

	if( !target || src->m != target->m || !src->prev || !target->prev )
		return 0;

	if( battle_config.ksprotection && sd && mob_ksprotected(src, target) )
		return 0;

	// Normally not needed because clif.cpp checks for it, but the at/char/script commands don't! [Skotlex]
	if(ud->skilltimer != INVALID_TIMER && skill_id != SA_CASTCANCEL && skill_id != SO_SPELLFIST)
		return 0;

	if(skill->inf2[INF2_NOTARGETSELF] && src->id == target_id)
		return 0;

	if(!status_check_skilluse(src, target, skill_id, 0))
		return 0;

	// Fail if the targetted skill is near NPC [Cydh]
	if(skill->inf2[INF2_DISABLENEARNPC] && !ignore_range && skill_isNotOk_npcRange(src,skill_id,skill_lv,target->x,target->y)) {
		if (sd)
			clif_skill_fail( *sd, skill_id );

		return 0;
	}

	status_data* tstatus = status_get_status_data(*target);

	// Record the status of the previous skill)
	if(sd) {
		switch(skill_id) {
			case SA_CASTCANCEL:
				if(ud->skill_id != skill_id) {
					sd->skill_id_old = ud->skill_id;
					sd->skill_lv_old = ud->skill_lv;
				}
				break;
			case BD_ENCORE:
				// Prevent using the dance skill if you no longer have the skill in your tree.
				if(!sd->skill_id_dance || pc_checkskill(sd,sd->skill_id_dance)<=0) {
					clif_skill_fail( *sd, skill_id );
					return 0;
				}

				sd->skill_id_old = skill_id;
				break;
			case WL_WHITEIMPRISON:
				if( battle_check_target(src,target,BCT_SELF|BCT_ENEMY) < 0 ) {
					clif_skill_fail( *sd, skill_id, USESKILL_FAIL_TOTARGET );
					return 0;
				}
				break;
			case MG_FIREBOLT:
			case MG_LIGHTNINGBOLT:
			case MG_COLDBOLT:
				sd->skill_id_old = skill_id;
				sd->skill_lv_old = skill_lv;
				break;
			case CR_DEVOTION:
				if (target->type == BL_PC) {
					uint8 i = 0, count = min(skill_lv, MAX_DEVOTION);

					ARR_FIND(0, count, i, sd->devotion[i] == target_id);
					if (i == count) {
						ARR_FIND(0, count, i, sd->devotion[i] == 0);
						if (i == count) { // No free slots, skill Fail
							clif_skill_fail( *sd, skill_id );
							return 0;
						}
					}
				}
				break;
			case RL_C_MARKER: {
					uint8 i = 0;

					ARR_FIND(0, MAX_SKILL_CRIMSON_MARKER, i, sd->c_marker[i] == target_id);
					if (i == MAX_SKILL_CRIMSON_MARKER) {
						ARR_FIND(0, MAX_SKILL_CRIMSON_MARKER, i, sd->c_marker[i] == 0);
						if (i == MAX_SKILL_CRIMSON_MARKER) { // No free slots, skill Fail
							clif_skill_fail( *sd, skill_id );
							return 0;
						}
					}
				}
				break;
			case DK_SERVANT_W_SIGN: {
					uint8 i = 0, count = min(skill_lv, MAX_SERVANT_SIGN);

					ARR_FIND( 0, count, i, sd->servant_sign[i] == target_id );

					// Already targetted
					if( i < count ){
						break;
					}

					ARR_FIND( 0, count, i, sd->servant_sign[i] == 0 );

					// No free slots
					if( i == count ){
						clif_skill_fail( *sd, skill_id );
						return 0;
					}
				}
				break;
			case TR_RETROSPECTION:
				// Prevent using the song skill if you no longer have the skill in your tree.
				if (!sd->skill_id_song || pc_checkskill(sd, sd->skill_id_song) <= 0) {
					clif_skill_fail( *sd, skill_id );
					return 0;
				}

				sd->skill_id_old = skill_id;
				break;
		}

		if (!skill_check_condition_castbegin(*sd, skill_id, skill_lv))
			return 0;
	}

	if( src->type == BL_MOB ) {
		switch( skill_id ) {
			case NPC_SUMMONSLAVE:
			case NPC_SUMMONMONSTER:
			case NPC_DEATHSUMMON:
			case AL_TELEPORT:
				if( ((TBL_MOB*)src)->master_id && ((TBL_MOB*)src)->special_state.ai )
					return 0;
		}
	}

	range = skill_get_range2(src, skill_id, skill_lv, true); // Skill cast distance from database

	// New action request received, delete previous action request if not executed yet
	if(ud->stepaction || ud->steptimer != INVALID_TIMER)
		unit_stop_stepaction(src);
	// Remember the skill request from the client while walking to the next cell
	if(src->type == BL_PC && ud->walktimer != INVALID_TIMER && (!battle_check_range(src, target, range-1) || ignore_range)) {
		ud->stepaction = true;
		ud->target_to = target_id;
		ud->stepskill_id = skill_id;
		ud->stepskill_lv = skill_lv;
		return 0; // Attacking will be handled by unit_walktoxy_timer in this case
	}

	// Check range when not using skill on yourself or is a combo-skill during attack
	// (these are supposed to always have the same range as your attack)
	if( src->type != BL_NPC && !ignore_range && src->id != target_id && (!combo || ud->attacktimer == INVALID_TIMER) ) {
		if( skill_get_state(ud->skill_id) == ST_MOVE_ENABLE ) {
			if( !unit_can_reach_bl(src, target, range + 1, 1, nullptr, nullptr) )
				return 0; // Walk-path check failed.
		} else if( src->type == BL_MER && skill_id == MA_REMOVETRAP ) {
			if( !battle_check_range(battle_get_master(src), target, range + 1) )
				return 0; // Aegis calc remove trap based on Master position, ignoring mercenary O.O
		} else if( !battle_check_range(src, target, range) )
			return 0; // Arrow-path check failed.
	}

	if (!combo) // Stop attack on non-combo skills [Skotlex]
		unit_stop_attack(src);

	ud->state.skillcastcancel = castcancel;

	// Combo: Used to signal force cast now.
	combo = 0;

	switch(skill_id) {
		case ALL_RESURRECTION:
			if(battle_check_undead(tstatus->race,tstatus->def_ele))
				combo = 1;
			else if (!status_isdead(*target))
				return 0; // Can't cast on non-dead characters.
		break;
#ifndef RENEWAL
		case MO_FINGEROFFENSIVE:
			if(sd)
				casttime += casttime * min(skill_lv, sd->spiritball);
		break;
#endif
		case MO_EXTREMITYFIST:
			if (sc && sc->getSCE(SC_COMBO) &&
			   (sc->getSCE(SC_COMBO)->val1 == MO_COMBOFINISH ||
				sc->getSCE(SC_COMBO)->val1 == CH_CHAINCRUSH))
				casttime = -1;
			combo = 1;
		break;
		case SR_GATEOFHELL:
		case SR_TIGERCANNON:
			if (sc && sc->getSCE(SC_COMBO) &&
			   sc->getSCE(SC_COMBO)->val1 == SR_FALLENEMPIRE)
				casttime = -1;
			combo = 1;
		break;
		case SA_SPELLBREAKER:
			combo = 1;
		break;
#ifndef RENEWAL_CAST
		case ST_CHASEWALK:
			if (sc && sc->getSCE(SC_CHASEWALK))
				casttime = -1;
		break;
#endif
		case TK_RUN:
			if (sc && sc->getSCE(SC_RUN))
				casttime = -1;
		break;
#ifndef RENEWAL
		case HP_BASILICA:
			if( sc && sc->getSCE(SC_BASILICA) )
				casttime = -1; // No Casting time on basilica cancel
		break;
#endif
#ifndef RENEWAL_CAST
		case KN_CHARGEATK:
		{
			uint32 k = (distance_bl(src,target)-1)/3; //Range 0-3: 500ms, Range 4-6: 1000ms, Range 7+: 1500ms
			if(k > 2)
				k = 2;
			casttime += casttime * k;
		}
		break;
#endif
		case GD_EMERGENCYCALL: // Emergency Call double cast when the user has learned Leap [Daegaladh]
			if (sd && (pc_checkskill(sd,TK_HIGHJUMP) || pc_checkskill(sd,SU_LOPE) >= 3))
				casttime *= 2;
			break;
		case RA_WUGDASH:
			if (sc && sc->getSCE(SC_WUGDASH))
				casttime = -1;
			break;
		case DK_SERVANT_W_PHANTOM: { // Stops servants from being consumed on unmarked targets.
				status_change *tsc = status_get_sc(target);

				// Only allow to attack if the enemy has a sign mark given by the caster.
				if( tsc == nullptr || tsc->getSCE(SC_SERVANT_SIGN) == nullptr || tsc->getSCE(SC_SERVANT_SIGN)->val1 != src->id ){
					if (sd)
						clif_skill_fail( *sd, skill_id, USESKILL_FAIL );
					return 0;
				}
			}
			break;
		case EL_WIND_SLASH:
		case EL_HURRICANE:
		case EL_TYPOON_MIS:
		case EL_STONE_HAMMER:
		case EL_ROCK_CRUSHER:
		case EL_STONE_RAIN:
		case EL_ICE_NEEDLE:
		case EL_WATER_SCREW:
		case EL_TIDAL_WEAPON:
			if( src->type == BL_ELEM ) {
				sd = BL_CAST(BL_PC, battle_get_master(src));
				if( sd && sd->skill_id_old == SO_EL_ACTION ) {
					casttime = -1;
					sd->skill_id_old = 0;
				}
			}
			break;
	}

	// Moved here to prevent Suffragium from ending if skill fails
#ifndef RENEWAL_CAST
	casttime = skill_castfix_sc(src, casttime, skill_get_castnodex(skill_id));
#else
	casttime = skill_vfcastfix(src, casttime, skill_id, skill_lv);
#endif

	// Need TK_RUN or WUGDASH handler to be done before that, see bugreport:6026
	if(!ud->state.running){
		// Even though this is not how official works but this will do the trick. bugreport:6829
		unit_stop_walking( src, USW_FIXPOS );
	}

	// SC_MAGICPOWER needs to switch states at start of cast
#ifndef RENEWAL
	skill_toggle_magicpower(src, skill_id);
#endif

	// In official this is triggered even if no cast time.
	clif_skillcasting(src, src->id, target_id, 0,0, skill_id, skill_lv, skill_get_ele(skill_id, skill_lv), casttime);

	if (sd != nullptr && target->type == BL_MOB
#ifndef RENEWAL
		&& (casttime > 0 || combo > 0)
#endif
	) {
		TBL_MOB *md = (TBL_MOB*)target;

		mobskill_event(md, src, tick, -1); // Cast targetted skill event.

		if ((status_has_mode(tstatus,MD_CASTSENSORIDLE) || status_has_mode(tstatus,MD_CASTSENSORCHASE)) && battle_check_target(target, src, BCT_ENEMY) > 0 && !ignore_range) {
			switch (md->state.skillstate) {
				case MSS_RUSH:
				case MSS_FOLLOW:
					if (!status_has_mode(tstatus,MD_CASTSENSORCHASE))
						break;

					md->target_id = src->id;
					md->state.aggressive = status_has_mode(tstatus,MD_ANGRY)?1:0;
					break;
				case MSS_IDLE:
				case MSS_WALK:
					if (!status_has_mode(tstatus,MD_CASTSENSORIDLE))
						break;

					md->target_id = src->id;
					md->state.aggressive = status_has_mode(tstatus,MD_ANGRY)?1:0;
					break;
			}
		}
	}

	if( casttime <= 0 )
		ud->state.skillcastcancel = 0;

	if( sd ) {
		switch( skill_id ) {
			case CG_ARROWVULCAN:
				sd->canequip_tick = tick + casttime;
				break;
		}
	}

	ud->skilltarget  = target_id;
	ud->skillx       = 0;
	ud->skilly       = 0;
	ud->skill_id      = skill_id;
	ud->skill_lv      = skill_lv;

	// Set attack and act delays
	// Please note that the call below relies on ud->skill_id being set!
	unit_set_attackdelay(*src, tick, DELAY_EVENT_CASTBEGIN_ID);
	// Apply cast time and general delays
	unit_set_castdelay(*ud, tick, (skill_get_cast(skill_id, skill_lv) != 0) ? casttime : 0);

	if( sc ) {
		// These 3 status do not stack, so it's efficient to use if-else
 		if( sc->getSCE(SC_CLOAKING) && !(sc->getSCE(SC_CLOAKING)->val4&4) && skill_id != AS_CLOAKING && skill_id != SHC_SHADOW_STAB) {
			status_change_end(src, SC_CLOAKING);

			if (!src->prev)
				return 0; // Warped away!
		} else if( sc->getSCE(SC_CLOAKINGEXCEED) && !(sc->getSCE(SC_CLOAKINGEXCEED)->val4&4) && skill_id != GC_CLOAKINGEXCEED && skill_id != SHC_SHADOW_STAB  && skill_id != SHC_SAVAGE_IMPACT ) {
			status_change_end(src,SC_CLOAKINGEXCEED);

			if (!src->prev)
				return 0;
		} else if (sc->getSCE(SC_NEWMOON) && skill_id != SJ_NEWMOONKICK) {
			status_change_end(src, SC_NEWMOON);
			if (!src->prev)
				return 0; // Warped away!
		}
	}


	if( casttime > 0 ) {
		ud->skilltimer = add_timer( tick+casttime, skill_castend_id, src->id, 0 );

		if( sd && (pc_checkskill(sd,SA_FREECAST) > 0 || skill_id == LG_EXEEDBREAK) )
			status_calc_bl(&sd->bl, { SCB_SPEED, SCB_ASPD });
	} else {
 
		/** [keitenai] Speed Hack Protection **/
		if (sd && battle_config.KEITENAI_DELAY_SYSTEM) {
			sd->k_tick_c = 0;
			sd->kdelay = 0;

			switch (skill_id) {
			case SM_BASH:                          if (k_tick_check(sd, sd->spamtick_SM_BASH,                          sd->spamcount_SM_BASH,                          battle_config.kd_SM_BASH,                          battle_config.kdw_SM_BASH))                          { sd->spamcount_SM_BASH = sd->k_tick_c; return 0; }                          sd->spamcount_SM_BASH = 0;                          sd->spamtick_SM_BASH = tick + sd->kdelay;                          break;
			case SM_MAGNUM:                        if (k_tick_check(sd, sd->spamtick_SM_MAGNUM,                        sd->spamcount_SM_MAGNUM,                        battle_config.kd_SM_MAGNUM,                        battle_config.kdw_SM_MAGNUM))                        { sd->spamcount_SM_MAGNUM = sd->k_tick_c; return 0; }                        sd->spamcount_SM_MAGNUM = 0;                        sd->spamtick_SM_MAGNUM = tick + sd->kdelay;                        break;
			case MG_NAPALMBEAT:                    if (k_tick_check(sd, sd->spamtick_MG_NAPALMBEAT,                    sd->spamcount_MG_NAPALMBEAT,                    battle_config.kd_MG_NAPALMBEAT,                    battle_config.kdw_MG_NAPALMBEAT))                    { sd->spamcount_MG_NAPALMBEAT = sd->k_tick_c; return 0; }                    sd->spamcount_MG_NAPALMBEAT = 0;                    sd->spamtick_MG_NAPALMBEAT = tick + sd->kdelay;                    break;
			case MG_SOULSTRIKE:                    if (k_tick_check(sd, sd->spamtick_MG_SOULSTRIKE,                    sd->spamcount_MG_SOULSTRIKE,                    battle_config.kd_MG_SOULSTRIKE,                    battle_config.kdw_MG_SOULSTRIKE))                    { sd->spamcount_MG_SOULSTRIKE = sd->k_tick_c; return 0; }                    sd->spamcount_MG_SOULSTRIKE = 0;                    sd->spamtick_MG_SOULSTRIKE = tick + sd->kdelay;                    break;
			case MG_COLDBOLT:                      if (k_tick_check(sd, sd->spamtick_MG_COLDBOLT,                      sd->spamcount_MG_COLDBOLT,                      battle_config.kd_MG_COLDBOLT,                      battle_config.kdw_MG_COLDBOLT))                      { sd->spamcount_MG_COLDBOLT = sd->k_tick_c; return 0; }                      sd->spamcount_MG_COLDBOLT = 0;                      sd->spamtick_MG_COLDBOLT = tick + sd->kdelay;                      break;
			case MG_FROSTDIVER:                    if (k_tick_check(sd, sd->spamtick_MG_FROSTDIVER,                    sd->spamcount_MG_FROSTDIVER,                    battle_config.kd_MG_FROSTDIVER,                    battle_config.kdw_MG_FROSTDIVER))                    { sd->spamcount_MG_FROSTDIVER = sd->k_tick_c; return 0; }                    sd->spamcount_MG_FROSTDIVER = 0;                    sd->spamtick_MG_FROSTDIVER = tick + sd->kdelay;                    break;
			case MG_STONECURSE:                    if (k_tick_check(sd, sd->spamtick_MG_STONECURSE,                    sd->spamcount_MG_STONECURSE,                    battle_config.kd_MG_STONECURSE,                    battle_config.kdw_MG_STONECURSE))                    { sd->spamcount_MG_STONECURSE = sd->k_tick_c; return 0; }                    sd->spamcount_MG_STONECURSE = 0;                    sd->spamtick_MG_STONECURSE = tick + sd->kdelay;                    break;
			case MG_FIREBALL:                      if (k_tick_check(sd, sd->spamtick_MG_FIREBALL,                      sd->spamcount_MG_FIREBALL,                      battle_config.kd_MG_FIREBALL,                      battle_config.kdw_MG_FIREBALL))                      { sd->spamcount_MG_FIREBALL = sd->k_tick_c; return 0; }                      sd->spamcount_MG_FIREBALL = 0;                      sd->spamtick_MG_FIREBALL = tick + sd->kdelay;                      break;
			case MG_FIREWALL:                      if (k_tick_check(sd, sd->spamtick_MG_FIREWALL,                      sd->spamcount_MG_FIREWALL,                      battle_config.kd_MG_FIREWALL,                      battle_config.kdw_MG_FIREWALL))                      { sd->spamcount_MG_FIREWALL = sd->k_tick_c; return 0; }                      sd->spamcount_MG_FIREWALL = 0;                      sd->spamtick_MG_FIREWALL = tick + sd->kdelay;                      break;
			case MG_FIREBOLT:                      if (k_tick_check(sd, sd->spamtick_MG_FIREBOLT,                      sd->spamcount_MG_FIREBOLT,                      battle_config.kd_MG_FIREBOLT,                      battle_config.kdw_MG_FIREBOLT))                      { sd->spamcount_MG_FIREBOLT = sd->k_tick_c; return 0; }                      sd->spamcount_MG_FIREBOLT = 0;                      sd->spamtick_MG_FIREBOLT = tick + sd->kdelay;                      break;
			case MG_LIGHTNINGBOLT:                 if (k_tick_check(sd, sd->spamtick_MG_LIGHTNINGBOLT,                 sd->spamcount_MG_LIGHTNINGBOLT,                 battle_config.kd_MG_LIGHTNINGBOLT,                 battle_config.kdw_MG_LIGHTNINGBOLT))                 { sd->spamcount_MG_LIGHTNINGBOLT = sd->k_tick_c; return 0; }                 sd->spamcount_MG_LIGHTNINGBOLT = 0;                 sd->spamtick_MG_LIGHTNINGBOLT = tick + sd->kdelay;                 break;
			case MG_THUNDERSTORM:                  if (k_tick_check(sd, sd->spamtick_MG_THUNDERSTORM,                  sd->spamcount_MG_THUNDERSTORM,                  battle_config.kd_MG_THUNDERSTORM,                  battle_config.kdw_MG_THUNDERSTORM))                  { sd->spamcount_MG_THUNDERSTORM = sd->k_tick_c; return 0; }                  sd->spamcount_MG_THUNDERSTORM = 0;                  sd->spamtick_MG_THUNDERSTORM = tick + sd->kdelay;                  break;
			case AL_HEAL:                          if (k_tick_check(sd, sd->spamtick_AL_HEAL,                          sd->spamcount_AL_HEAL,                          battle_config.kd_AL_HEAL,                          battle_config.kdw_AL_HEAL))                          { sd->spamcount_AL_HEAL = sd->k_tick_c; return 0; }                          sd->spamcount_AL_HEAL = 0;                          sd->spamtick_AL_HEAL = tick + sd->kdelay;                          break;
			case AL_DECAGI:                        if (k_tick_check(sd, sd->spamtick_AL_DECAGI,                        sd->spamcount_AL_DECAGI,                        battle_config.kd_AL_DECAGI,                        battle_config.kdw_AL_DECAGI))                        { sd->spamcount_AL_DECAGI = sd->k_tick_c; return 0; }                        sd->spamcount_AL_DECAGI = 0;                        sd->spamtick_AL_DECAGI = tick + sd->kdelay;                        break;
			case AL_CRUCIS:                        if (k_tick_check(sd, sd->spamtick_AL_CRUCIS,                        sd->spamcount_AL_CRUCIS,                        battle_config.kd_AL_CRUCIS,                        battle_config.kdw_AL_CRUCIS))                        { sd->spamcount_AL_CRUCIS = sd->k_tick_c; return 0; }                        sd->spamcount_AL_CRUCIS = 0;                        sd->spamtick_AL_CRUCIS = tick + sd->kdelay;                        break;
			case MC_MAMMONITE:                     if (k_tick_check(sd, sd->spamtick_MC_MAMMONITE,                     sd->spamcount_MC_MAMMONITE,                     battle_config.kd_MC_MAMMONITE,                     battle_config.kdw_MC_MAMMONITE))                     { sd->spamcount_MC_MAMMONITE = sd->k_tick_c; return 0; }                     sd->spamcount_MC_MAMMONITE = 0;                     sd->spamtick_MC_MAMMONITE = tick + sd->kdelay;                     break;
			case AC_DOUBLE:                        if (k_tick_check(sd, sd->spamtick_AC_DOUBLE,                        sd->spamcount_AC_DOUBLE,                        battle_config.kd_AC_DOUBLE,                        battle_config.kdw_AC_DOUBLE))                        { sd->spamcount_AC_DOUBLE = sd->k_tick_c; return 0; }                        sd->spamcount_AC_DOUBLE = 0;                        sd->spamtick_AC_DOUBLE = tick + sd->kdelay;                        break;
			case AC_SHOWER:                        if (k_tick_check(sd, sd->spamtick_AC_SHOWER,                        sd->spamcount_AC_SHOWER,                        battle_config.kd_AC_SHOWER,                        battle_config.kdw_AC_SHOWER))                        { sd->spamcount_AC_SHOWER = sd->k_tick_c; return 0; }                        sd->spamcount_AC_SHOWER = 0;                        sd->spamtick_AC_SHOWER = tick + sd->kdelay;                        break;
			case TF_POISON:                        if (k_tick_check(sd, sd->spamtick_TF_POISON,                        sd->spamcount_TF_POISON,                        battle_config.kd_TF_POISON,                        battle_config.kdw_TF_POISON))                        { sd->spamcount_TF_POISON = sd->k_tick_c; return 0; }                        sd->spamcount_TF_POISON = 0;                        sd->spamtick_TF_POISON = tick + sd->kdelay;                        break;
			case KN_PIERCE:                        if (k_tick_check(sd, sd->spamtick_KN_PIERCE,                        sd->spamcount_KN_PIERCE,                        battle_config.kd_KN_PIERCE,                        battle_config.kdw_KN_PIERCE))                        { sd->spamcount_KN_PIERCE = sd->k_tick_c; return 0; }                        sd->spamcount_KN_PIERCE = 0;                        sd->spamtick_KN_PIERCE = tick + sd->kdelay;                        break;
			case KN_BRANDISHSPEAR:                 if (k_tick_check(sd, sd->spamtick_KN_BRANDISHSPEAR,                 sd->spamcount_KN_BRANDISHSPEAR,                 battle_config.kd_KN_BRANDISHSPEAR,                 battle_config.kdw_KN_BRANDISHSPEAR))                 { sd->spamcount_KN_BRANDISHSPEAR = sd->k_tick_c; return 0; }                 sd->spamcount_KN_BRANDISHSPEAR = 0;                 sd->spamtick_KN_BRANDISHSPEAR = tick + sd->kdelay;                 break;
			case KN_SPEARSTAB:                     if (k_tick_check(sd, sd->spamtick_KN_SPEARSTAB,                     sd->spamcount_KN_SPEARSTAB,                     battle_config.kd_KN_SPEARSTAB,                     battle_config.kdw_KN_SPEARSTAB))                     { sd->spamcount_KN_SPEARSTAB = sd->k_tick_c; return 0; }                     sd->spamcount_KN_SPEARSTAB = 0;                     sd->spamtick_KN_SPEARSTAB = tick + sd->kdelay;                     break;
			case KN_SPEARBOOMERANG:                if (k_tick_check(sd, sd->spamtick_KN_SPEARBOOMERANG,                sd->spamcount_KN_SPEARBOOMERANG,                battle_config.kd_KN_SPEARBOOMERANG,                battle_config.kdw_KN_SPEARBOOMERANG))                { sd->spamcount_KN_SPEARBOOMERANG = sd->k_tick_c; return 0; }                sd->spamcount_KN_SPEARBOOMERANG = 0;                sd->spamtick_KN_SPEARBOOMERANG = tick + sd->kdelay;                break;
			case KN_BOWLINGBASH:                   if (k_tick_check(sd, sd->spamtick_KN_BOWLINGBASH,                   sd->spamcount_KN_BOWLINGBASH,                   battle_config.kd_KN_BOWLINGBASH,                   battle_config.kdw_KN_BOWLINGBASH))                   { sd->spamcount_KN_BOWLINGBASH = sd->k_tick_c; return 0; }                   sd->spamcount_KN_BOWLINGBASH = 0;                   sd->spamtick_KN_BOWLINGBASH = tick + sd->kdelay;                   break;
			case PR_LEXDIVINA:                     if (k_tick_check(sd, sd->spamtick_PR_LEXDIVINA,                     sd->spamcount_PR_LEXDIVINA,                     battle_config.kd_PR_LEXDIVINA,                     battle_config.kdw_PR_LEXDIVINA))                     { sd->spamcount_PR_LEXDIVINA = sd->k_tick_c; return 0; }                     sd->spamcount_PR_LEXDIVINA = 0;                     sd->spamtick_PR_LEXDIVINA = tick + sd->kdelay;                     break;
			case PR_TURNUNDEAD:                    if (k_tick_check(sd, sd->spamtick_PR_TURNUNDEAD,                    sd->spamcount_PR_TURNUNDEAD,                    battle_config.kd_PR_TURNUNDEAD,                    battle_config.kdw_PR_TURNUNDEAD))                    { sd->spamcount_PR_TURNUNDEAD = sd->k_tick_c; return 0; }                    sd->spamcount_PR_TURNUNDEAD = 0;                    sd->spamtick_PR_TURNUNDEAD = tick + sd->kdelay;                    break;
			case PR_LEXAETERNA:                    if (k_tick_check(sd, sd->spamtick_PR_LEXAETERNA,                    sd->spamcount_PR_LEXAETERNA,                    battle_config.kd_PR_LEXAETERNA,                    battle_config.kdw_PR_LEXAETERNA))                    { sd->spamcount_PR_LEXAETERNA = sd->k_tick_c; return 0; }                    sd->spamcount_PR_LEXAETERNA = 0;                    sd->spamtick_PR_LEXAETERNA = tick + sd->kdelay;                    break;
			case PR_MAGNUS:                        if (k_tick_check(sd, sd->spamtick_PR_MAGNUS,                        sd->spamcount_PR_MAGNUS,                        battle_config.kd_PR_MAGNUS,                        battle_config.kdw_PR_MAGNUS))                        { sd->spamcount_PR_MAGNUS = sd->k_tick_c; return 0; }                        sd->spamcount_PR_MAGNUS = 0;                        sd->spamtick_PR_MAGNUS = tick + sd->kdelay;                        break;
			case WZ_FIREPILLAR:                    if (k_tick_check(sd, sd->spamtick_WZ_FIREPILLAR,                    sd->spamcount_WZ_FIREPILLAR,                    battle_config.kd_WZ_FIREPILLAR,                    battle_config.kdw_WZ_FIREPILLAR))                    { sd->spamcount_WZ_FIREPILLAR = sd->k_tick_c; return 0; }                    sd->spamcount_WZ_FIREPILLAR = 0;                    sd->spamtick_WZ_FIREPILLAR = tick + sd->kdelay;                    break;
			case WZ_SIGHTRASHER:                   if (k_tick_check(sd, sd->spamtick_WZ_SIGHTRASHER,                   sd->spamcount_WZ_SIGHTRASHER,                   battle_config.kd_WZ_SIGHTRASHER,                   battle_config.kdw_WZ_SIGHTRASHER))                   { sd->spamcount_WZ_SIGHTRASHER = sd->k_tick_c; return 0; }                   sd->spamcount_WZ_SIGHTRASHER = 0;                   sd->spamtick_WZ_SIGHTRASHER = tick + sd->kdelay;                   break;
			case WZ_FIREIVY:                       if (k_tick_check(sd, sd->spamtick_WZ_FIREIVY,                       sd->spamcount_WZ_FIREIVY,                       battle_config.kd_WZ_FIREIVY,                       battle_config.kdw_WZ_FIREIVY))                       { sd->spamcount_WZ_FIREIVY = sd->k_tick_c; return 0; }                       sd->spamcount_WZ_FIREIVY = 0;                       sd->spamtick_WZ_FIREIVY = tick + sd->kdelay;                       break;
			case WZ_METEOR:                        if (k_tick_check(sd, sd->spamtick_WZ_METEOR,                        sd->spamcount_WZ_METEOR,                        battle_config.kd_WZ_METEOR,                        battle_config.kdw_WZ_METEOR))                        { sd->spamcount_WZ_METEOR = sd->k_tick_c; return 0; }                        sd->spamcount_WZ_METEOR = 0;                        sd->spamtick_WZ_METEOR = tick + sd->kdelay;                        break;
			case WZ_JUPITEL:                       if (k_tick_check(sd, sd->spamtick_WZ_JUPITEL,                       sd->spamcount_WZ_JUPITEL,                       battle_config.kd_WZ_JUPITEL,                       battle_config.kdw_WZ_JUPITEL))                       { sd->spamcount_WZ_JUPITEL = sd->k_tick_c; return 0; }                       sd->spamcount_WZ_JUPITEL = 0;                       sd->spamtick_WZ_JUPITEL = tick + sd->kdelay;                       break;
			case WZ_VERMILION:                     if (k_tick_check(sd, sd->spamtick_WZ_VERMILION,                     sd->spamcount_WZ_VERMILION,                     battle_config.kd_WZ_VERMILION,                     battle_config.kdw_WZ_VERMILION))                     { sd->spamcount_WZ_VERMILION = sd->k_tick_c; return 0; }                     sd->spamcount_WZ_VERMILION = 0;                     sd->spamtick_WZ_VERMILION = tick + sd->kdelay;                     break;
			case WZ_WATERBALL:                     if (k_tick_check(sd, sd->spamtick_WZ_WATERBALL,                     sd->spamcount_WZ_WATERBALL,                     battle_config.kd_WZ_WATERBALL,                     battle_config.kdw_WZ_WATERBALL))                     { sd->spamcount_WZ_WATERBALL = sd->k_tick_c; return 0; }                     sd->spamcount_WZ_WATERBALL = 0;                     sd->spamtick_WZ_WATERBALL = tick + sd->kdelay;                     break;
			case WZ_ICEWALL:                       if (k_tick_check(sd, sd->spamtick_WZ_ICEWALL,                       sd->spamcount_WZ_ICEWALL,                       battle_config.kd_WZ_ICEWALL,                       battle_config.kdw_WZ_ICEWALL))                       { sd->spamcount_WZ_ICEWALL = sd->k_tick_c; return 0; }                       sd->spamcount_WZ_ICEWALL = 0;                       sd->spamtick_WZ_ICEWALL = tick + sd->kdelay;                       break;
			case WZ_FROSTNOVA:                     if (k_tick_check(sd, sd->spamtick_WZ_FROSTNOVA,                     sd->spamcount_WZ_FROSTNOVA,                     battle_config.kd_WZ_FROSTNOVA,                     battle_config.kdw_WZ_FROSTNOVA))                     { sd->spamcount_WZ_FROSTNOVA = sd->k_tick_c; return 0; }                     sd->spamcount_WZ_FROSTNOVA = 0;                     sd->spamtick_WZ_FROSTNOVA = tick + sd->kdelay;                     break;
			case WZ_STORMGUST:                     if (k_tick_check(sd, sd->spamtick_WZ_STORMGUST,                     sd->spamcount_WZ_STORMGUST,                     battle_config.kd_WZ_STORMGUST,                     battle_config.kdw_WZ_STORMGUST))                     { sd->spamcount_WZ_STORMGUST = sd->k_tick_c; return 0; }                     sd->spamcount_WZ_STORMGUST = 0;                     sd->spamtick_WZ_STORMGUST = tick + sd->kdelay;                     break;
			case WZ_EARTHSPIKE:                    if (k_tick_check(sd, sd->spamtick_WZ_EARTHSPIKE,                    sd->spamcount_WZ_EARTHSPIKE,                    battle_config.kd_WZ_EARTHSPIKE,                    battle_config.kdw_WZ_EARTHSPIKE))                    { sd->spamcount_WZ_EARTHSPIKE = sd->k_tick_c; return 0; }                    sd->spamcount_WZ_EARTHSPIKE = 0;                    sd->spamtick_WZ_EARTHSPIKE = tick + sd->kdelay;                    break;
			case WZ_HEAVENDRIVE:                   if (k_tick_check(sd, sd->spamtick_WZ_HEAVENDRIVE,                   sd->spamcount_WZ_HEAVENDRIVE,                   battle_config.kd_WZ_HEAVENDRIVE,                   battle_config.kdw_WZ_HEAVENDRIVE))                   { sd->spamcount_WZ_HEAVENDRIVE = sd->k_tick_c; return 0; }                   sd->spamcount_WZ_HEAVENDRIVE = 0;                   sd->spamtick_WZ_HEAVENDRIVE = tick + sd->kdelay;                   break;
			case WZ_QUAGMIRE:                      if (k_tick_check(sd, sd->spamtick_WZ_QUAGMIRE,                      sd->spamcount_WZ_QUAGMIRE,                      battle_config.kd_WZ_QUAGMIRE,                      battle_config.kdw_WZ_QUAGMIRE))                      { sd->spamcount_WZ_QUAGMIRE = sd->k_tick_c; return 0; }                      sd->spamcount_WZ_QUAGMIRE = 0;                      sd->spamtick_WZ_QUAGMIRE = tick + sd->kdelay;                      break;
			case WZ_ESTIMATION:                    if (k_tick_check(sd, sd->spamtick_WZ_ESTIMATION,                    sd->spamcount_WZ_ESTIMATION,                    battle_config.kd_WZ_ESTIMATION,                    battle_config.kdw_WZ_ESTIMATION))                    { sd->spamcount_WZ_ESTIMATION = sd->k_tick_c; return 0; }                    sd->spamcount_WZ_ESTIMATION = 0;                    sd->spamtick_WZ_ESTIMATION = tick + sd->kdelay;                    break;
			case BS_HAMMERFALL:                    if (k_tick_check(sd, sd->spamtick_BS_HAMMERFALL,                    sd->spamcount_BS_HAMMERFALL,                    battle_config.kd_BS_HAMMERFALL,                    battle_config.kdw_BS_HAMMERFALL))                    { sd->spamcount_BS_HAMMERFALL = sd->k_tick_c; return 0; }                    sd->spamcount_BS_HAMMERFALL = 0;                    sd->spamtick_BS_HAMMERFALL = tick + sd->kdelay;                    break;
			case HT_BLITZBEAT:                     if (k_tick_check(sd, sd->spamtick_HT_BLITZBEAT,                     sd->spamcount_HT_BLITZBEAT,                     battle_config.kd_HT_BLITZBEAT,                     battle_config.kdw_HT_BLITZBEAT))                     { sd->spamcount_HT_BLITZBEAT = sd->k_tick_c; return 0; }                     sd->spamcount_HT_BLITZBEAT = 0;                     sd->spamtick_HT_BLITZBEAT = tick + sd->kdelay;                     break;
			case AS_SONICBLOW:                     if (k_tick_check(sd, sd->spamtick_AS_SONICBLOW,                     sd->spamcount_AS_SONICBLOW,                     battle_config.kd_AS_SONICBLOW,                     battle_config.kdw_AS_SONICBLOW))                     { sd->spamcount_AS_SONICBLOW = sd->k_tick_c; return 0; }                     sd->spamcount_AS_SONICBLOW = 0;                     sd->spamtick_AS_SONICBLOW = tick + sd->kdelay;                     break;
			case AS_GRIMTOOTH:                     if (k_tick_check(sd, sd->spamtick_AS_GRIMTOOTH,                     sd->spamcount_AS_GRIMTOOTH,                     battle_config.kd_AS_GRIMTOOTH,                     battle_config.kdw_AS_GRIMTOOTH))                     { sd->spamcount_AS_GRIMTOOTH = sd->k_tick_c; return 0; }                     sd->spamcount_AS_GRIMTOOTH = 0;                     sd->spamtick_AS_GRIMTOOTH = tick + sd->kdelay;                     break;
			case AC_CHARGEARROW:                   if (k_tick_check(sd, sd->spamtick_AC_CHARGEARROW,                   sd->spamcount_AC_CHARGEARROW,                   battle_config.kd_AC_CHARGEARROW,                   battle_config.kdw_AC_CHARGEARROW))                   { sd->spamcount_AC_CHARGEARROW = sd->k_tick_c; return 0; }                   sd->spamcount_AC_CHARGEARROW = 0;                   sd->spamtick_AC_CHARGEARROW = tick + sd->kdelay;                   break;
			case TF_BACKSLIDING:                   if (k_tick_check(sd, sd->spamtick_TF_BACKSLIDING,                   sd->spamcount_TF_BACKSLIDING,                   battle_config.kd_TF_BACKSLIDING,                   battle_config.kdw_TF_BACKSLIDING))                   { sd->spamcount_TF_BACKSLIDING = sd->k_tick_c; return 0; }                   sd->spamcount_TF_BACKSLIDING = 0;                   sd->spamtick_TF_BACKSLIDING = tick + sd->kdelay;                   break;
			case MC_CARTREVOLUTION:                if (k_tick_check(sd, sd->spamtick_MC_CARTREVOLUTION,                sd->spamcount_MC_CARTREVOLUTION,                battle_config.kd_MC_CARTREVOLUTION,                battle_config.kdw_MC_CARTREVOLUTION))                { sd->spamcount_MC_CARTREVOLUTION = sd->k_tick_c; return 0; }                sd->spamcount_MC_CARTREVOLUTION = 0;                sd->spamtick_MC_CARTREVOLUTION = tick + sd->kdelay;                break;
			case AL_HOLYLIGHT:                     if (k_tick_check(sd, sd->spamtick_AL_HOLYLIGHT,                     sd->spamcount_AL_HOLYLIGHT,                     battle_config.kd_AL_HOLYLIGHT,                     battle_config.kdw_AL_HOLYLIGHT))                     { sd->spamcount_AL_HOLYLIGHT = sd->k_tick_c; return 0; }                     sd->spamcount_AL_HOLYLIGHT = 0;                     sd->spamtick_AL_HOLYLIGHT = tick + sd->kdelay;                     break;
			case RG_BACKSTAP:                      if (k_tick_check(sd, sd->spamtick_RG_BACKSTAP,                      sd->spamcount_RG_BACKSTAP,                      battle_config.kd_RG_BACKSTAP,                      battle_config.kdw_RG_BACKSTAP))                      { sd->spamcount_RG_BACKSTAP = sd->k_tick_c; return 0; }                      sd->spamcount_RG_BACKSTAP = 0;                      sd->spamtick_RG_BACKSTAP = tick + sd->kdelay;                      break;
			case RG_RAID:                          if (k_tick_check(sd, sd->spamtick_RG_RAID,                          sd->spamcount_RG_RAID,                          battle_config.kd_RG_RAID,                          battle_config.kdw_RG_RAID))                          { sd->spamcount_RG_RAID = sd->k_tick_c; return 0; }                          sd->spamcount_RG_RAID = 0;                          sd->spamtick_RG_RAID = tick + sd->kdelay;                          break;
			case RG_GRAFFITI:                      if (k_tick_check(sd, sd->spamtick_RG_GRAFFITI,                      sd->spamcount_RG_GRAFFITI,                      battle_config.kd_RG_GRAFFITI,                      battle_config.kdw_RG_GRAFFITI))                      { sd->spamcount_RG_GRAFFITI = sd->k_tick_c; return 0; }                      sd->spamcount_RG_GRAFFITI = 0;                      sd->spamtick_RG_GRAFFITI = tick + sd->kdelay;                      break;
			case RG_FLAGGRAFFITI:                  if (k_tick_check(sd, sd->spamtick_RG_FLAGGRAFFITI,                  sd->spamcount_RG_FLAGGRAFFITI,                  battle_config.kd_RG_FLAGGRAFFITI,                  battle_config.kdw_RG_FLAGGRAFFITI))                  { sd->spamcount_RG_FLAGGRAFFITI = sd->k_tick_c; return 0; }                  sd->spamcount_RG_FLAGGRAFFITI = 0;                  sd->spamtick_RG_FLAGGRAFFITI = tick + sd->kdelay;                  break;
			case RG_COMPULSION:                    if (k_tick_check(sd, sd->spamtick_RG_COMPULSION,                    sd->spamcount_RG_COMPULSION,                    battle_config.kd_RG_COMPULSION,                    battle_config.kdw_RG_COMPULSION))                    { sd->spamcount_RG_COMPULSION = sd->k_tick_c; return 0; }                    sd->spamcount_RG_COMPULSION = 0;                    sd->spamtick_RG_COMPULSION = tick + sd->kdelay;                    break;
			case RG_PLAGIARISM:                    if (k_tick_check(sd, sd->spamtick_RG_PLAGIARISM,                    sd->spamcount_RG_PLAGIARISM,                    battle_config.kd_RG_PLAGIARISM,                    battle_config.kdw_RG_PLAGIARISM))                    { sd->spamcount_RG_PLAGIARISM = sd->k_tick_c; return 0; }                    sd->spamcount_RG_PLAGIARISM = 0;                    sd->spamtick_RG_PLAGIARISM = tick + sd->kdelay;                    break;
			case AM_DEMONSTRATION:                 if (k_tick_check(sd, sd->spamtick_AM_DEMONSTRATION,                 sd->spamcount_AM_DEMONSTRATION,                 battle_config.kd_AM_DEMONSTRATION,                 battle_config.kdw_AM_DEMONSTRATION))                 { sd->spamcount_AM_DEMONSTRATION = sd->k_tick_c; return 0; }                 sd->spamcount_AM_DEMONSTRATION = 0;                 sd->spamtick_AM_DEMONSTRATION = tick + sd->kdelay;                 break;
			case AM_ACIDTERROR:                    if (k_tick_check(sd, sd->spamtick_AM_ACIDTERROR,                    sd->spamcount_AM_ACIDTERROR,                    battle_config.kd_AM_ACIDTERROR,                    battle_config.kdw_AM_ACIDTERROR))                    { sd->spamcount_AM_ACIDTERROR = sd->k_tick_c; return 0; }                    sd->spamcount_AM_ACIDTERROR = 0;                    sd->spamtick_AM_ACIDTERROR = tick + sd->kdelay;                    break;
			case AM_POTIONPITCHER:                 if (k_tick_check(sd, sd->spamtick_AM_POTIONPITCHER,                 sd->spamcount_AM_POTIONPITCHER,                 battle_config.kd_AM_POTIONPITCHER,                 battle_config.kdw_AM_POTIONPITCHER))                 { sd->spamcount_AM_POTIONPITCHER = sd->k_tick_c; return 0; }                 sd->spamcount_AM_POTIONPITCHER = 0;                 sd->spamtick_AM_POTIONPITCHER = tick + sd->kdelay;                 break;
			case AM_CANNIBALIZE:                   if (k_tick_check(sd, sd->spamtick_AM_CANNIBALIZE,                   sd->spamcount_AM_CANNIBALIZE,                   battle_config.kd_AM_CANNIBALIZE,                   battle_config.kdw_AM_CANNIBALIZE))                   { sd->spamcount_AM_CANNIBALIZE = sd->k_tick_c; return 0; }                   sd->spamcount_AM_CANNIBALIZE = 0;                   sd->spamtick_AM_CANNIBALIZE = tick + sd->kdelay;                   break;
			case AM_SPHEREMINE:                    if (k_tick_check(sd, sd->spamtick_AM_SPHEREMINE,                    sd->spamcount_AM_SPHEREMINE,                    battle_config.kd_AM_SPHEREMINE,                    battle_config.kdw_AM_SPHEREMINE))                    { sd->spamcount_AM_SPHEREMINE = sd->k_tick_c; return 0; }                    sd->spamcount_AM_SPHEREMINE = 0;                    sd->spamtick_AM_SPHEREMINE = tick + sd->kdelay;                    break;
			case AM_FLAMECONTROL:                  if (k_tick_check(sd, sd->spamtick_AM_FLAMECONTROL,                  sd->spamcount_AM_FLAMECONTROL,                  battle_config.kd_AM_FLAMECONTROL,                  battle_config.kdw_AM_FLAMECONTROL))                  { sd->spamcount_AM_FLAMECONTROL = sd->k_tick_c; return 0; }                  sd->spamcount_AM_FLAMECONTROL = 0;                  sd->spamtick_AM_FLAMECONTROL = tick + sd->kdelay;                  break;
			case AM_DRILLMASTER:                   if (k_tick_check(sd, sd->spamtick_AM_DRILLMASTER,                   sd->spamcount_AM_DRILLMASTER,                   battle_config.kd_AM_DRILLMASTER,                   battle_config.kdw_AM_DRILLMASTER))                   { sd->spamcount_AM_DRILLMASTER = sd->k_tick_c; return 0; }                   sd->spamcount_AM_DRILLMASTER = 0;                   sd->spamtick_AM_DRILLMASTER = tick + sd->kdelay;                   break;
			case CR_SHIELDBOOMERANG:               if (k_tick_check(sd, sd->spamtick_CR_SHIELDBOOMERANG,               sd->spamcount_CR_SHIELDBOOMERANG,               battle_config.kd_CR_SHIELDBOOMERANG,               battle_config.kdw_CR_SHIELDBOOMERANG))               { sd->spamcount_CR_SHIELDBOOMERANG = sd->k_tick_c; return 0; }               sd->spamcount_CR_SHIELDBOOMERANG = 0;               sd->spamtick_CR_SHIELDBOOMERANG = tick + sd->kdelay;               break;
			case CR_HOLYCROSS:                     if (k_tick_check(sd, sd->spamtick_CR_HOLYCROSS,                     sd->spamcount_CR_HOLYCROSS,                     battle_config.kd_CR_HOLYCROSS,                     battle_config.kdw_CR_HOLYCROSS))                     { sd->spamcount_CR_HOLYCROSS = sd->k_tick_c; return 0; }                     sd->spamcount_CR_HOLYCROSS = 0;                     sd->spamtick_CR_HOLYCROSS = tick + sd->kdelay;                     break;
			case CR_GRANDCROSS:                    if (k_tick_check(sd, sd->spamtick_CR_GRANDCROSS,                    sd->spamcount_CR_GRANDCROSS,                    battle_config.kd_CR_GRANDCROSS,                    battle_config.kdw_CR_GRANDCROSS))                    { sd->spamcount_CR_GRANDCROSS = sd->k_tick_c; return 0; }                    sd->spamcount_CR_GRANDCROSS = 0;                    sd->spamtick_CR_GRANDCROSS = tick + sd->kdelay;                    break;
			case MO_CALLSPIRITS:                   if (k_tick_check(sd, sd->spamtick_MO_CALLSPIRITS,                   sd->spamcount_MO_CALLSPIRITS,                   battle_config.kd_MO_CALLSPIRITS,                   battle_config.kdw_MO_CALLSPIRITS))                   { sd->spamcount_MO_CALLSPIRITS = sd->k_tick_c; return 0; }                   sd->spamcount_MO_CALLSPIRITS = 0;                   sd->spamtick_MO_CALLSPIRITS = tick + sd->kdelay;                   break;
			case MO_ABSORBSPIRITS:                 if (k_tick_check(sd, sd->spamtick_MO_ABSORBSPIRITS,                 sd->spamcount_MO_ABSORBSPIRITS,                 battle_config.kd_MO_ABSORBSPIRITS,                 battle_config.kdw_MO_ABSORBSPIRITS))                 { sd->spamcount_MO_ABSORBSPIRITS = sd->k_tick_c; return 0; }                 sd->spamcount_MO_ABSORBSPIRITS = 0;                 sd->spamtick_MO_ABSORBSPIRITS = tick + sd->kdelay;                 break;
			case MO_BODYRELOCATION:                if (k_tick_check(sd, sd->spamtick_MO_BODYRELOCATION,                sd->spamcount_MO_BODYRELOCATION,                battle_config.kd_MO_BODYRELOCATION,                battle_config.kdw_MO_BODYRELOCATION))                { sd->spamcount_MO_BODYRELOCATION = sd->k_tick_c; return 0; }                sd->spamcount_MO_BODYRELOCATION = 0;                sd->spamtick_MO_BODYRELOCATION = tick + sd->kdelay;                break;
			case MO_INVESTIGATE:                   if (k_tick_check(sd, sd->spamtick_MO_INVESTIGATE,                   sd->spamcount_MO_INVESTIGATE,                   battle_config.kd_MO_INVESTIGATE,                   battle_config.kdw_MO_INVESTIGATE))                   { sd->spamcount_MO_INVESTIGATE = sd->k_tick_c; return 0; }                   sd->spamcount_MO_INVESTIGATE = 0;                   sd->spamtick_MO_INVESTIGATE = tick + sd->kdelay;                   break;
			case MO_FINGEROFFENSIVE:               if (k_tick_check(sd, sd->spamtick_MO_FINGEROFFENSIVE,               sd->spamcount_MO_FINGEROFFENSIVE,               battle_config.kd_MO_FINGEROFFENSIVE,               battle_config.kdw_MO_FINGEROFFENSIVE))               { sd->spamcount_MO_FINGEROFFENSIVE = sd->k_tick_c; return 0; }               sd->spamcount_MO_FINGEROFFENSIVE = 0;               sd->spamtick_MO_FINGEROFFENSIVE = tick + sd->kdelay;               break;
			case MO_EXPLOSIONSPIRITS:              if (k_tick_check(sd, sd->spamtick_MO_EXPLOSIONSPIRITS,              sd->spamcount_MO_EXPLOSIONSPIRITS,              battle_config.kd_MO_EXPLOSIONSPIRITS,              battle_config.kdw_MO_EXPLOSIONSPIRITS))              { sd->spamcount_MO_EXPLOSIONSPIRITS = sd->k_tick_c; return 0; }              sd->spamcount_MO_EXPLOSIONSPIRITS = 0;              sd->spamtick_MO_EXPLOSIONSPIRITS = tick + sd->kdelay;              break;
			case MO_EXTREMITYFIST:                 if (k_tick_check(sd, sd->spamtick_MO_EXTREMITYFIST,                 sd->spamcount_MO_EXTREMITYFIST,                 battle_config.kd_MO_EXTREMITYFIST,                 battle_config.kdw_MO_EXTREMITYFIST))                 { sd->spamcount_MO_EXTREMITYFIST = sd->k_tick_c; return 0; }                 sd->spamcount_MO_EXTREMITYFIST = 0;                 sd->spamtick_MO_EXTREMITYFIST = tick + sd->kdelay;                 break;
			case MO_CHAINCOMBO:                    if (k_tick_check(sd, sd->spamtick_MO_CHAINCOMBO,                    sd->spamcount_MO_CHAINCOMBO,                    battle_config.kd_MO_CHAINCOMBO,                    battle_config.kdw_MO_CHAINCOMBO))                    { sd->spamcount_MO_CHAINCOMBO = sd->k_tick_c; return 0; }                    sd->spamcount_MO_CHAINCOMBO = 0;                    sd->spamtick_MO_CHAINCOMBO = tick + sd->kdelay;                    break;
			case MO_COMBOFINISH:                   if (k_tick_check(sd, sd->spamtick_MO_COMBOFINISH,                   sd->spamcount_MO_COMBOFINISH,                   battle_config.kd_MO_COMBOFINISH,                   battle_config.kdw_MO_COMBOFINISH))                   { sd->spamcount_MO_COMBOFINISH = sd->k_tick_c; return 0; }                   sd->spamcount_MO_COMBOFINISH = 0;                   sd->spamtick_MO_COMBOFINISH = tick + sd->kdelay;                   break;
			case SA_CASTCANCEL:                    if (k_tick_check(sd, sd->spamtick_SA_CASTCANCEL,                    sd->spamcount_SA_CASTCANCEL,                    battle_config.kd_SA_CASTCANCEL,                    battle_config.kdw_SA_CASTCANCEL))                    { sd->spamcount_SA_CASTCANCEL = sd->k_tick_c; return 0; }                    sd->spamcount_SA_CASTCANCEL = 0;                    sd->spamtick_SA_CASTCANCEL = tick + sd->kdelay;                    break;
			case SA_SPELLBREAKER:                  if (k_tick_check(sd, sd->spamtick_SA_SPELLBREAKER,                  sd->spamcount_SA_SPELLBREAKER,                  battle_config.kd_SA_SPELLBREAKER,                  battle_config.kdw_SA_SPELLBREAKER))                  { sd->spamcount_SA_SPELLBREAKER = sd->k_tick_c; return 0; }                  sd->spamcount_SA_SPELLBREAKER = 0;                  sd->spamtick_SA_SPELLBREAKER = tick + sd->kdelay;                  break;
			case SA_DISPELL:                       if (k_tick_check(sd, sd->spamtick_SA_DISPELL,                       sd->spamcount_SA_DISPELL,                       battle_config.kd_SA_DISPELL,                       battle_config.kdw_SA_DISPELL))                       { sd->spamcount_SA_DISPELL = sd->k_tick_c; return 0; }                       sd->spamcount_SA_DISPELL = 0;                       sd->spamtick_SA_DISPELL = tick + sd->kdelay;                       break;
			case SA_ABRACADABRA:                   if (k_tick_check(sd, sd->spamtick_SA_ABRACADABRA,                   sd->spamcount_SA_ABRACADABRA,                   battle_config.kd_SA_ABRACADABRA,                   battle_config.kdw_SA_ABRACADABRA))                   { sd->spamcount_SA_ABRACADABRA = sd->k_tick_c; return 0; }                   sd->spamcount_SA_ABRACADABRA = 0;                   sd->spamtick_SA_ABRACADABRA = tick + sd->kdelay;                   break;
			case SA_MONOCELL:                      if (k_tick_check(sd, sd->spamtick_SA_MONOCELL,                      sd->spamcount_SA_MONOCELL,                      battle_config.kd_SA_MONOCELL,                      battle_config.kdw_SA_MONOCELL))                      { sd->spamcount_SA_MONOCELL = sd->k_tick_c; return 0; }                      sd->spamcount_SA_MONOCELL = 0;                      sd->spamtick_SA_MONOCELL = tick + sd->kdelay;                      break;
			case SA_CLASSCHANGE:                   if (k_tick_check(sd, sd->spamtick_SA_CLASSCHANGE,                   sd->spamcount_SA_CLASSCHANGE,                   battle_config.kd_SA_CLASSCHANGE,                   battle_config.kdw_SA_CLASSCHANGE))                   { sd->spamcount_SA_CLASSCHANGE = sd->k_tick_c; return 0; }                   sd->spamcount_SA_CLASSCHANGE = 0;                   sd->spamtick_SA_CLASSCHANGE = tick + sd->kdelay;                   break;
			case SA_SUMMONMONSTER:                 if (k_tick_check(sd, sd->spamtick_SA_SUMMONMONSTER,                 sd->spamcount_SA_SUMMONMONSTER,                 battle_config.kd_SA_SUMMONMONSTER,                 battle_config.kdw_SA_SUMMONMONSTER))                 { sd->spamcount_SA_SUMMONMONSTER = sd->k_tick_c; return 0; }                 sd->spamcount_SA_SUMMONMONSTER = 0;                 sd->spamtick_SA_SUMMONMONSTER = tick + sd->kdelay;                 break;
			case SA_REVERSEORCISH:                 if (k_tick_check(sd, sd->spamtick_SA_REVERSEORCISH,                 sd->spamcount_SA_REVERSEORCISH,                 battle_config.kd_SA_REVERSEORCISH,                 battle_config.kdw_SA_REVERSEORCISH))                 { sd->spamcount_SA_REVERSEORCISH = sd->k_tick_c; return 0; }                 sd->spamcount_SA_REVERSEORCISH = 0;                 sd->spamtick_SA_REVERSEORCISH = tick + sd->kdelay;                 break;
			case SA_DEATH:                         if (k_tick_check(sd, sd->spamtick_SA_DEATH,                         sd->spamcount_SA_DEATH,                         battle_config.kd_SA_DEATH,                         battle_config.kdw_SA_DEATH))                         { sd->spamcount_SA_DEATH = sd->k_tick_c; return 0; }                         sd->spamcount_SA_DEATH = 0;                         sd->spamtick_SA_DEATH = tick + sd->kdelay;                         break;
			case SA_FORTUNE:                       if (k_tick_check(sd, sd->spamtick_SA_FORTUNE,                       sd->spamcount_SA_FORTUNE,                       battle_config.kd_SA_FORTUNE,                       battle_config.kdw_SA_FORTUNE))                       { sd->spamcount_SA_FORTUNE = sd->k_tick_c; return 0; }                       sd->spamcount_SA_FORTUNE = 0;                       sd->spamtick_SA_FORTUNE = tick + sd->kdelay;                       break;
			case SA_TAMINGMONSTER:                 if (k_tick_check(sd, sd->spamtick_SA_TAMINGMONSTER,                 sd->spamcount_SA_TAMINGMONSTER,                 battle_config.kd_SA_TAMINGMONSTER,                 battle_config.kdw_SA_TAMINGMONSTER))                 { sd->spamcount_SA_TAMINGMONSTER = sd->k_tick_c; return 0; }                 sd->spamcount_SA_TAMINGMONSTER = 0;                 sd->spamtick_SA_TAMINGMONSTER = tick + sd->kdelay;                 break;
			case SA_QUESTION:                      if (k_tick_check(sd, sd->spamtick_SA_QUESTION,                      sd->spamcount_SA_QUESTION,                      battle_config.kd_SA_QUESTION,                      battle_config.kdw_SA_QUESTION))                      { sd->spamcount_SA_QUESTION = sd->k_tick_c; return 0; }                      sd->spamcount_SA_QUESTION = 0;                      sd->spamtick_SA_QUESTION = tick + sd->kdelay;                      break;
			case SA_GRAVITY:                       if (k_tick_check(sd, sd->spamtick_SA_GRAVITY,                       sd->spamcount_SA_GRAVITY,                       battle_config.kd_SA_GRAVITY,                       battle_config.kdw_SA_GRAVITY))                       { sd->spamcount_SA_GRAVITY = sd->k_tick_c; return 0; }                       sd->spamcount_SA_GRAVITY = 0;                       sd->spamtick_SA_GRAVITY = tick + sd->kdelay;                       break;
			case SA_LEVELUP:                       if (k_tick_check(sd, sd->spamtick_SA_LEVELUP,                       sd->spamcount_SA_LEVELUP,                       battle_config.kd_SA_LEVELUP,                       battle_config.kdw_SA_LEVELUP))                       { sd->spamcount_SA_LEVELUP = sd->k_tick_c; return 0; }                       sd->spamcount_SA_LEVELUP = 0;                       sd->spamtick_SA_LEVELUP = tick + sd->kdelay;                       break;
			case SA_INSTANTDEATH:                  if (k_tick_check(sd, sd->spamtick_SA_INSTANTDEATH,                  sd->spamcount_SA_INSTANTDEATH,                  battle_config.kd_SA_INSTANTDEATH,                  battle_config.kdw_SA_INSTANTDEATH))                  { sd->spamcount_SA_INSTANTDEATH = sd->k_tick_c; return 0; }                  sd->spamcount_SA_INSTANTDEATH = 0;                  sd->spamtick_SA_INSTANTDEATH = tick + sd->kdelay;                  break;
			case SA_FULLRECOVERY:                  if (k_tick_check(sd, sd->spamtick_SA_FULLRECOVERY,                  sd->spamcount_SA_FULLRECOVERY,                  battle_config.kd_SA_FULLRECOVERY,                  battle_config.kdw_SA_FULLRECOVERY))                  { sd->spamcount_SA_FULLRECOVERY = sd->k_tick_c; return 0; }                  sd->spamcount_SA_FULLRECOVERY = 0;                  sd->spamtick_SA_FULLRECOVERY = tick + sd->kdelay;                  break;
			case SA_COMA:                          if (k_tick_check(sd, sd->spamtick_SA_COMA,                          sd->spamcount_SA_COMA,                          battle_config.kd_SA_COMA,                          battle_config.kdw_SA_COMA))                          { sd->spamcount_SA_COMA = sd->k_tick_c; return 0; }                          sd->spamcount_SA_COMA = 0;                          sd->spamtick_SA_COMA = tick + sd->kdelay;                          break;
			case BD_ADAPTATION:                    if (k_tick_check(sd, sd->spamtick_BD_ADAPTATION,                    sd->spamcount_BD_ADAPTATION,                    battle_config.kd_BD_ADAPTATION,                    battle_config.kdw_BD_ADAPTATION))                    { sd->spamcount_BD_ADAPTATION = sd->k_tick_c; return 0; }                    sd->spamcount_BD_ADAPTATION = 0;                    sd->spamtick_BD_ADAPTATION = tick + sd->kdelay;                    break;
			case BD_ENCORE:                        if (k_tick_check(sd, sd->spamtick_BD_ENCORE,                        sd->spamcount_BD_ENCORE,                        battle_config.kd_BD_ENCORE,                        battle_config.kdw_BD_ENCORE))                        { sd->spamcount_BD_ENCORE = sd->k_tick_c; return 0; }                        sd->spamcount_BD_ENCORE = 0;                        sd->spamtick_BD_ENCORE = tick + sd->kdelay;                        break;
			case BD_LULLABY:                       if (k_tick_check(sd, sd->spamtick_BD_LULLABY,                       sd->spamcount_BD_LULLABY,                       battle_config.kd_BD_LULLABY,                       battle_config.kdw_BD_LULLABY))                       { sd->spamcount_BD_LULLABY = sd->k_tick_c; return 0; }                       sd->spamcount_BD_LULLABY = 0;                       sd->spamtick_BD_LULLABY = tick + sd->kdelay;                       break;
			case BD_RICHMANKIM:                    if (k_tick_check(sd, sd->spamtick_BD_RICHMANKIM,                    sd->spamcount_BD_RICHMANKIM,                    battle_config.kd_BD_RICHMANKIM,                    battle_config.kdw_BD_RICHMANKIM))                    { sd->spamcount_BD_RICHMANKIM = sd->k_tick_c; return 0; }                    sd->spamcount_BD_RICHMANKIM = 0;                    sd->spamtick_BD_RICHMANKIM = tick + sd->kdelay;                    break;
			case BA_MUSICALSTRIKE:                 if (k_tick_check(sd, sd->spamtick_BA_MUSICALSTRIKE,                 sd->spamcount_BA_MUSICALSTRIKE,                 battle_config.kd_BA_MUSICALSTRIKE,                 battle_config.kdw_BA_MUSICALSTRIKE))                 { sd->spamcount_BA_MUSICALSTRIKE = sd->k_tick_c; return 0; }                 sd->spamcount_BA_MUSICALSTRIKE = 0;                 sd->spamtick_BA_MUSICALSTRIKE = tick + sd->kdelay;                 break;
			case BA_DISSONANCE:                    if (k_tick_check(sd, sd->spamtick_BA_DISSONANCE,                    sd->spamcount_BA_DISSONANCE,                    battle_config.kd_BA_DISSONANCE,                    battle_config.kdw_BA_DISSONANCE))                    { sd->spamcount_BA_DISSONANCE = sd->k_tick_c; return 0; }                    sd->spamcount_BA_DISSONANCE = 0;                    sd->spamtick_BA_DISSONANCE = tick + sd->kdelay;                    break;
			case BA_FROSTJOKER:                    if (k_tick_check(sd, sd->spamtick_BA_FROSTJOKER,                    sd->spamcount_BA_FROSTJOKER,                    battle_config.kd_BA_FROSTJOKER,                    battle_config.kdw_BA_FROSTJOKER))                    { sd->spamcount_BA_FROSTJOKER = sd->k_tick_c; return 0; }                    sd->spamcount_BA_FROSTJOKER = 0;                    sd->spamtick_BA_FROSTJOKER = tick + sd->kdelay;                    break;
			case BA_WHISTLE:                       if (k_tick_check(sd, sd->spamtick_BA_WHISTLE,                       sd->spamcount_BA_WHISTLE,                       battle_config.kd_BA_WHISTLE,                       battle_config.kdw_BA_WHISTLE))                       { sd->spamcount_BA_WHISTLE = sd->k_tick_c; return 0; }                       sd->spamcount_BA_WHISTLE = 0;                       sd->spamtick_BA_WHISTLE = tick + sd->kdelay;                       break;
			case BA_ASSASSINCROSS:                 if (k_tick_check(sd, sd->spamtick_BA_ASSASSINCROSS,                 sd->spamcount_BA_ASSASSINCROSS,                 battle_config.kd_BA_ASSASSINCROSS,                 battle_config.kdw_BA_ASSASSINCROSS))                 { sd->spamcount_BA_ASSASSINCROSS = sd->k_tick_c; return 0; }                 sd->spamcount_BA_ASSASSINCROSS = 0;                 sd->spamtick_BA_ASSASSINCROSS = tick + sd->kdelay;                 break;
			case BA_POEMBRAGI:                     if (k_tick_check(sd, sd->spamtick_BA_POEMBRAGI,                     sd->spamcount_BA_POEMBRAGI,                     battle_config.kd_BA_POEMBRAGI,                     battle_config.kdw_BA_POEMBRAGI))                     { sd->spamcount_BA_POEMBRAGI = sd->k_tick_c; return 0; }                     sd->spamcount_BA_POEMBRAGI = 0;                     sd->spamtick_BA_POEMBRAGI = tick + sd->kdelay;                     break;
			case BA_APPLEIDUN:                     if (k_tick_check(sd, sd->spamtick_BA_APPLEIDUN,                     sd->spamcount_BA_APPLEIDUN,                     battle_config.kd_BA_APPLEIDUN,                     battle_config.kdw_BA_APPLEIDUN))                     { sd->spamcount_BA_APPLEIDUN = sd->k_tick_c; return 0; }                     sd->spamcount_BA_APPLEIDUN = 0;                     sd->spamtick_BA_APPLEIDUN = tick + sd->kdelay;                     break;
			case DC_THROWARROW:                    if (k_tick_check(sd, sd->spamtick_DC_THROWARROW,                    sd->spamcount_DC_THROWARROW,                    battle_config.kd_DC_THROWARROW,                    battle_config.kdw_DC_THROWARROW))                    { sd->spamcount_DC_THROWARROW = sd->k_tick_c; return 0; }                    sd->spamcount_DC_THROWARROW = 0;                    sd->spamtick_DC_THROWARROW = tick + sd->kdelay;                    break;
			case DC_UGLYDANCE:                     if (k_tick_check(sd, sd->spamtick_DC_UGLYDANCE,                     sd->spamcount_DC_UGLYDANCE,                     battle_config.kd_DC_UGLYDANCE,                     battle_config.kdw_DC_UGLYDANCE))                     { sd->spamcount_DC_UGLYDANCE = sd->k_tick_c; return 0; }                     sd->spamcount_DC_UGLYDANCE = 0;                     sd->spamtick_DC_UGLYDANCE = tick + sd->kdelay;                     break;
			case DC_SCREAM:                        if (k_tick_check(sd, sd->spamtick_DC_SCREAM,                        sd->spamcount_DC_SCREAM,                        battle_config.kd_DC_SCREAM,                        battle_config.kdw_DC_SCREAM))                        { sd->spamcount_DC_SCREAM = sd->k_tick_c; return 0; }                        sd->spamcount_DC_SCREAM = 0;                        sd->spamtick_DC_SCREAM = tick + sd->kdelay;                        break;
			case DC_HUMMING:                       if (k_tick_check(sd, sd->spamtick_DC_HUMMING,                       sd->spamcount_DC_HUMMING,                       battle_config.kd_DC_HUMMING,                       battle_config.kdw_DC_HUMMING))                       { sd->spamcount_DC_HUMMING = sd->k_tick_c; return 0; }                       sd->spamcount_DC_HUMMING = 0;                       sd->spamtick_DC_HUMMING = tick + sd->kdelay;                       break;
			case DC_DONTFORGETME:                  if (k_tick_check(sd, sd->spamtick_DC_DONTFORGETME,                  sd->spamcount_DC_DONTFORGETME,                  battle_config.kd_DC_DONTFORGETME,                  battle_config.kdw_DC_DONTFORGETME))                  { sd->spamcount_DC_DONTFORGETME = sd->k_tick_c; return 0; }                  sd->spamcount_DC_DONTFORGETME = 0;                  sd->spamtick_DC_DONTFORGETME = tick + sd->kdelay;                  break;
			case DC_FORTUNEKISS:                   if (k_tick_check(sd, sd->spamtick_DC_FORTUNEKISS,                   sd->spamcount_DC_FORTUNEKISS,                   battle_config.kd_DC_FORTUNEKISS,                   battle_config.kdw_DC_FORTUNEKISS))                   { sd->spamcount_DC_FORTUNEKISS = sd->k_tick_c; return 0; }                   sd->spamcount_DC_FORTUNEKISS = 0;                   sd->spamtick_DC_FORTUNEKISS = tick + sd->kdelay;                   break;
			case DC_SERVICEFORYOU:                 if (k_tick_check(sd, sd->spamtick_DC_SERVICEFORYOU,                 sd->spamcount_DC_SERVICEFORYOU,                 battle_config.kd_DC_SERVICEFORYOU,                 battle_config.kdw_DC_SERVICEFORYOU))                 { sd->spamcount_DC_SERVICEFORYOU = sd->k_tick_c; return 0; }                 sd->spamcount_DC_SERVICEFORYOU = 0;                 sd->spamtick_DC_SERVICEFORYOU = tick + sd->kdelay;                 break;
			case LK_FURY:                          if (k_tick_check(sd, sd->spamtick_LK_FURY,                          sd->spamcount_LK_FURY,                          battle_config.kd_LK_FURY,                          battle_config.kdw_LK_FURY))                          { sd->spamcount_LK_FURY = sd->k_tick_c; return 0; }                          sd->spamcount_LK_FURY = 0;                          sd->spamtick_LK_FURY = tick + sd->kdelay;                          break;
			case HW_MAGICCRASHER:                  if (k_tick_check(sd, sd->spamtick_HW_MAGICCRASHER,                  sd->spamcount_HW_MAGICCRASHER,                  battle_config.kd_HW_MAGICCRASHER,                  battle_config.kdw_HW_MAGICCRASHER))                  { sd->spamcount_HW_MAGICCRASHER = sd->k_tick_c; return 0; }                  sd->spamcount_HW_MAGICCRASHER = 0;                  sd->spamtick_HW_MAGICCRASHER = tick + sd->kdelay;                  break;
			case PA_PRESSURE:                      if (k_tick_check(sd, sd->spamtick_PA_PRESSURE,                      sd->spamcount_PA_PRESSURE,                      battle_config.kd_PA_PRESSURE,                      battle_config.kdw_PA_PRESSURE))                      { sd->spamcount_PA_PRESSURE = sd->k_tick_c; return 0; }                      sd->spamcount_PA_PRESSURE = 0;                      sd->spamtick_PA_PRESSURE = tick + sd->kdelay;                      break;
			case CH_PALMSTRIKE:                    if (k_tick_check(sd, sd->spamtick_CH_PALMSTRIKE,                    sd->spamcount_CH_PALMSTRIKE,                    battle_config.kd_CH_PALMSTRIKE,                    battle_config.kdw_CH_PALMSTRIKE))                    { sd->spamcount_CH_PALMSTRIKE = sd->k_tick_c; return 0; }                    sd->spamcount_CH_PALMSTRIKE = 0;                    sd->spamtick_CH_PALMSTRIKE = tick + sd->kdelay;                    break;
			case CH_TIGERFIST:                     if (k_tick_check(sd, sd->spamtick_CH_TIGERFIST,                     sd->spamcount_CH_TIGERFIST,                     battle_config.kd_CH_TIGERFIST,                     battle_config.kdw_CH_TIGERFIST))                     { sd->spamcount_CH_TIGERFIST = sd->k_tick_c; return 0; }                     sd->spamcount_CH_TIGERFIST = 0;                     sd->spamtick_CH_TIGERFIST = tick + sd->kdelay;                     break;
			case CH_CHAINCRUSH:                    if (k_tick_check(sd, sd->spamtick_CH_CHAINCRUSH,                    sd->spamcount_CH_CHAINCRUSH,                    battle_config.kd_CH_CHAINCRUSH,                    battle_config.kdw_CH_CHAINCRUSH))                    { sd->spamcount_CH_CHAINCRUSH = sd->k_tick_c; return 0; }                    sd->spamcount_CH_CHAINCRUSH = 0;                    sd->spamtick_CH_CHAINCRUSH = tick + sd->kdelay;                    break;
			case PF_SOULCHANGE:                    if (k_tick_check(sd, sd->spamtick_PF_SOULCHANGE,                    sd->spamcount_PF_SOULCHANGE,                    battle_config.kd_PF_SOULCHANGE,                    battle_config.kdw_PF_SOULCHANGE))                    { sd->spamcount_PF_SOULCHANGE = sd->k_tick_c; return 0; }                    sd->spamcount_PF_SOULCHANGE = 0;                    sd->spamtick_PF_SOULCHANGE = tick + sd->kdelay;                    break;
			case PF_SOULBURN:                      if (k_tick_check(sd, sd->spamtick_PF_SOULBURN,                      sd->spamcount_PF_SOULBURN,                      battle_config.kd_PF_SOULBURN,                      battle_config.kdw_PF_SOULBURN))                      { sd->spamcount_PF_SOULBURN = sd->k_tick_c; return 0; }                      sd->spamcount_PF_SOULBURN = 0;                      sd->spamtick_PF_SOULBURN = tick + sd->kdelay;                      break;
			case ASC_BREAKER:                      if (k_tick_check(sd, sd->spamtick_ASC_BREAKER,                      sd->spamcount_ASC_BREAKER,                      battle_config.kd_ASC_BREAKER,                      battle_config.kdw_ASC_BREAKER))                      { sd->spamcount_ASC_BREAKER = sd->k_tick_c; return 0; }                      sd->spamcount_ASC_BREAKER = 0;                      sd->spamtick_ASC_BREAKER = tick + sd->kdelay;                      break;
			case SN_FALCONASSAULT:                 if (k_tick_check(sd, sd->spamtick_SN_FALCONASSAULT,                 sd->spamcount_SN_FALCONASSAULT,                 battle_config.kd_SN_FALCONASSAULT,                 battle_config.kdw_SN_FALCONASSAULT))                 { sd->spamcount_SN_FALCONASSAULT = sd->k_tick_c; return 0; }                 sd->spamcount_SN_FALCONASSAULT = 0;                 sd->spamtick_SN_FALCONASSAULT = tick + sd->kdelay;                 break;
			case SN_SHARPSHOOTING:                 if (k_tick_check(sd, sd->spamtick_SN_SHARPSHOOTING,                 sd->spamcount_SN_SHARPSHOOTING,                 battle_config.kd_SN_SHARPSHOOTING,                 battle_config.kdw_SN_SHARPSHOOTING))                 { sd->spamcount_SN_SHARPSHOOTING = sd->k_tick_c; return 0; }                 sd->spamcount_SN_SHARPSHOOTING = 0;                 sd->spamtick_SN_SHARPSHOOTING = tick + sd->kdelay;                 break;
			case CR_ALCHEMY:                       if (k_tick_check(sd, sd->spamtick_CR_ALCHEMY,                       sd->spamcount_CR_ALCHEMY,                       battle_config.kd_CR_ALCHEMY,                       battle_config.kdw_CR_ALCHEMY))                       { sd->spamcount_CR_ALCHEMY = sd->k_tick_c; return 0; }                       sd->spamcount_CR_ALCHEMY = 0;                       sd->spamtick_CR_ALCHEMY = tick + sd->kdelay;                       break;
			case CR_SYNTHESISPOTION:               if (k_tick_check(sd, sd->spamtick_CR_SYNTHESISPOTION,               sd->spamcount_CR_SYNTHESISPOTION,               battle_config.kd_CR_SYNTHESISPOTION,               battle_config.kdw_CR_SYNTHESISPOTION))               { sd->spamcount_CR_SYNTHESISPOTION = sd->k_tick_c; return 0; }               sd->spamcount_CR_SYNTHESISPOTION = 0;               sd->spamtick_CR_SYNTHESISPOTION = tick + sd->kdelay;               break;
			case CG_ARROWVULCAN:                   if (k_tick_check(sd, sd->spamtick_CG_ARROWVULCAN,                   sd->spamcount_CG_ARROWVULCAN,                   battle_config.kd_CG_ARROWVULCAN,                   battle_config.kdw_CG_ARROWVULCAN))                   { sd->spamcount_CG_ARROWVULCAN = sd->k_tick_c; return 0; }                   sd->spamcount_CG_ARROWVULCAN = 0;                   sd->spamtick_CG_ARROWVULCAN = tick + sd->kdelay;                   break;
			case CG_MOONLIT:                       if (k_tick_check(sd, sd->spamtick_CG_MOONLIT,                       sd->spamcount_CG_MOONLIT,                       battle_config.kd_CG_MOONLIT,                       battle_config.kdw_CG_MOONLIT))                       { sd->spamcount_CG_MOONLIT = sd->k_tick_c; return 0; }                       sd->spamcount_CG_MOONLIT = 0;                       sd->spamtick_CG_MOONLIT = tick + sd->kdelay;                       break;
			case CG_MARIONETTE:                    if (k_tick_check(sd, sd->spamtick_CG_MARIONETTE,                    sd->spamcount_CG_MARIONETTE,                    battle_config.kd_CG_MARIONETTE,                    battle_config.kdw_CG_MARIONETTE))                    { sd->spamcount_CG_MARIONETTE = sd->k_tick_c; return 0; }                    sd->spamcount_CG_MARIONETTE = 0;                    sd->spamtick_CG_MARIONETTE = tick + sd->kdelay;                    break;
			case LK_SPIRALPIERCE:                  if (k_tick_check(sd, sd->spamtick_LK_SPIRALPIERCE,                  sd->spamcount_LK_SPIRALPIERCE,                  battle_config.kd_LK_SPIRALPIERCE,                  battle_config.kdw_LK_SPIRALPIERCE))                  { sd->spamcount_LK_SPIRALPIERCE = sd->k_tick_c; return 0; }                  sd->spamcount_LK_SPIRALPIERCE = 0;                  sd->spamtick_LK_SPIRALPIERCE = tick + sd->kdelay;                  break;
			case LK_HEADCRUSH:                     if (k_tick_check(sd, sd->spamtick_LK_HEADCRUSH,                     sd->spamcount_LK_HEADCRUSH,                     battle_config.kd_LK_HEADCRUSH,                     battle_config.kdw_LK_HEADCRUSH))                     { sd->spamcount_LK_HEADCRUSH = sd->k_tick_c; return 0; }                     sd->spamcount_LK_HEADCRUSH = 0;                     sd->spamtick_LK_HEADCRUSH = tick + sd->kdelay;                     break;
			case LK_JOINTBEAT:                     if (k_tick_check(sd, sd->spamtick_LK_JOINTBEAT,                     sd->spamcount_LK_JOINTBEAT,                     battle_config.kd_LK_JOINTBEAT,                     battle_config.kdw_LK_JOINTBEAT))                     { sd->spamcount_LK_JOINTBEAT = sd->k_tick_c; return 0; }                     sd->spamcount_LK_JOINTBEAT = 0;                     sd->spamtick_LK_JOINTBEAT = tick + sd->kdelay;                     break;
			case HW_NAPALMVULCAN:                  if (k_tick_check(sd, sd->spamtick_HW_NAPALMVULCAN,                  sd->spamcount_HW_NAPALMVULCAN,                  battle_config.kd_HW_NAPALMVULCAN,                  battle_config.kdw_HW_NAPALMVULCAN))                  { sd->spamcount_HW_NAPALMVULCAN = sd->k_tick_c; return 0; }                  sd->spamcount_HW_NAPALMVULCAN = 0;                  sd->spamtick_HW_NAPALMVULCAN = tick + sd->kdelay;                  break;
			case CH_SOULCOLLECT:                   if (k_tick_check(sd, sd->spamtick_CH_SOULCOLLECT,                   sd->spamcount_CH_SOULCOLLECT,                   battle_config.kd_CH_SOULCOLLECT,                   battle_config.kdw_CH_SOULCOLLECT))                   { sd->spamcount_CH_SOULCOLLECT = sd->k_tick_c; return 0; }                   sd->spamcount_CH_SOULCOLLECT = 0;                   sd->spamtick_CH_SOULCOLLECT = tick + sd->kdelay;                   break;
			case PF_MINDBREAKER:                   if (k_tick_check(sd, sd->spamtick_PF_MINDBREAKER,                   sd->spamcount_PF_MINDBREAKER,                   battle_config.kd_PF_MINDBREAKER,                   battle_config.kdw_PF_MINDBREAKER))                   { sd->spamcount_PF_MINDBREAKER = sd->k_tick_c; return 0; }                   sd->spamcount_PF_MINDBREAKER = 0;                   sd->spamtick_PF_MINDBREAKER = tick + sd->kdelay;                   break;
			case PF_SPIDERWEB:                     if (k_tick_check(sd, sd->spamtick_PF_SPIDERWEB,                     sd->spamcount_PF_SPIDERWEB,                     battle_config.kd_PF_SPIDERWEB,                     battle_config.kdw_PF_SPIDERWEB))                     { sd->spamcount_PF_SPIDERWEB = sd->k_tick_c; return 0; }                     sd->spamcount_PF_SPIDERWEB = 0;                     sd->spamtick_PF_SPIDERWEB = tick + sd->kdelay;                     break;
			case ASC_METEORASSAULT:                if (k_tick_check(sd, sd->spamtick_ASC_METEORASSAULT,                sd->spamcount_ASC_METEORASSAULT,                battle_config.kd_ASC_METEORASSAULT,                battle_config.kdw_ASC_METEORASSAULT))                { sd->spamcount_ASC_METEORASSAULT = sd->k_tick_c; return 0; }                sd->spamcount_ASC_METEORASSAULT = 0;                sd->spamtick_ASC_METEORASSAULT = tick + sd->kdelay;                break;
			case TK_STORMKICK:                     if (k_tick_check(sd, sd->spamtick_TK_STORMKICK,                     sd->spamcount_TK_STORMKICK,                     battle_config.kd_TK_STORMKICK,                     battle_config.kdw_TK_STORMKICK))                     { sd->spamcount_TK_STORMKICK = sd->k_tick_c; return 0; }                     sd->spamcount_TK_STORMKICK = 0;                     sd->spamtick_TK_STORMKICK = tick + sd->kdelay;                     break;
			case TK_DOWNKICK:                      if (k_tick_check(sd, sd->spamtick_TK_DOWNKICK,                      sd->spamcount_TK_DOWNKICK,                      battle_config.kd_TK_DOWNKICK,                      battle_config.kdw_TK_DOWNKICK))                      { sd->spamcount_TK_DOWNKICK = sd->k_tick_c; return 0; }                      sd->spamcount_TK_DOWNKICK = 0;                      sd->spamtick_TK_DOWNKICK = tick + sd->kdelay;                      break;
			case TK_TURNKICK:                      if (k_tick_check(sd, sd->spamtick_TK_TURNKICK,                      sd->spamcount_TK_TURNKICK,                      battle_config.kd_TK_TURNKICK,                      battle_config.kdw_TK_TURNKICK))                      { sd->spamcount_TK_TURNKICK = sd->k_tick_c; return 0; }                      sd->spamcount_TK_TURNKICK = 0;                      sd->spamtick_TK_TURNKICK = tick + sd->kdelay;                      break;
			case TK_JUMPKICK:                      if (k_tick_check(sd, sd->spamtick_TK_JUMPKICK,                      sd->spamcount_TK_JUMPKICK,                      battle_config.kd_TK_JUMPKICK,                      battle_config.kdw_TK_JUMPKICK))                      { sd->spamcount_TK_JUMPKICK = sd->k_tick_c; return 0; }                      sd->spamcount_TK_JUMPKICK = 0;                      sd->spamtick_TK_JUMPKICK = tick + sd->kdelay;                      break;
			case TK_POWER:                         if (k_tick_check(sd, sd->spamtick_TK_POWER,                         sd->spamcount_TK_POWER,                         battle_config.kd_TK_POWER,                         battle_config.kdw_TK_POWER))                         { sd->spamcount_TK_POWER = sd->k_tick_c; return 0; }                         sd->spamcount_TK_POWER = 0;                         sd->spamtick_TK_POWER = tick + sd->kdelay;                         break;
			case TK_HIGHJUMP:                      if (k_tick_check(sd, sd->spamtick_TK_HIGHJUMP,                      sd->spamcount_TK_HIGHJUMP,                      battle_config.kd_TK_HIGHJUMP,                      battle_config.kdw_TK_HIGHJUMP))                      { sd->spamcount_TK_HIGHJUMP = sd->k_tick_c; return 0; }                      sd->spamcount_TK_HIGHJUMP = 0;                      sd->spamtick_TK_HIGHJUMP = tick + sd->kdelay;                      break;
			case SL_KAIZEL:                        if (k_tick_check(sd, sd->spamtick_SL_KAIZEL,                        sd->spamcount_SL_KAIZEL,                        battle_config.kd_SL_KAIZEL,                        battle_config.kdw_SL_KAIZEL))                        { sd->spamcount_SL_KAIZEL = sd->k_tick_c; return 0; }                        sd->spamcount_SL_KAIZEL = 0;                        sd->spamtick_SL_KAIZEL = tick + sd->kdelay;                        break;
			case SL_KAAHI:                         if (k_tick_check(sd, sd->spamtick_SL_KAAHI,                         sd->spamcount_SL_KAAHI,                         battle_config.kd_SL_KAAHI,                         battle_config.kdw_SL_KAAHI))                         { sd->spamcount_SL_KAAHI = sd->k_tick_c; return 0; }                         sd->spamcount_SL_KAAHI = 0;                         sd->spamtick_SL_KAAHI = tick + sd->kdelay;                         break;
			case SL_KAUPE:                         if (k_tick_check(sd, sd->spamtick_SL_KAUPE,                         sd->spamcount_SL_KAUPE,                         battle_config.kd_SL_KAUPE,                         battle_config.kdw_SL_KAUPE))                         { sd->spamcount_SL_KAUPE = sd->k_tick_c; return 0; }                         sd->spamcount_SL_KAUPE = 0;                         sd->spamtick_SL_KAUPE = tick + sd->kdelay;                         break;
			case SL_KAITE:                         if (k_tick_check(sd, sd->spamtick_SL_KAITE,                         sd->spamcount_SL_KAITE,                         battle_config.kd_SL_KAITE,                         battle_config.kdw_SL_KAITE))                         { sd->spamcount_SL_KAITE = sd->k_tick_c; return 0; }                         sd->spamcount_SL_KAITE = 0;                         sd->spamtick_SL_KAITE = tick + sd->kdelay;                         break;
			case SL_KAINA:                         if (k_tick_check(sd, sd->spamtick_SL_KAINA,                         sd->spamcount_SL_KAINA,                         battle_config.kd_SL_KAINA,                         battle_config.kdw_SL_KAINA))                         { sd->spamcount_SL_KAINA = sd->k_tick_c; return 0; }                         sd->spamcount_SL_KAINA = 0;                         sd->spamtick_SL_KAINA = tick + sd->kdelay;                         break;
			case SL_STIN:                          if (k_tick_check(sd, sd->spamtick_SL_STIN,                          sd->spamcount_SL_STIN,                          battle_config.kd_SL_STIN,                          battle_config.kdw_SL_STIN))                          { sd->spamcount_SL_STIN = sd->k_tick_c; return 0; }                          sd->spamcount_SL_STIN = 0;                          sd->spamtick_SL_STIN = tick + sd->kdelay;                          break;
			case SL_STUN:                          if (k_tick_check(sd, sd->spamtick_SL_STUN,                          sd->spamcount_SL_STUN,                          battle_config.kd_SL_STUN,                          battle_config.kdw_SL_STUN))                          { sd->spamcount_SL_STUN = sd->k_tick_c; return 0; }                          sd->spamcount_SL_STUN = 0;                          sd->spamtick_SL_STUN = tick + sd->kdelay;                          break;
			case SL_SMA:                           if (k_tick_check(sd, sd->spamtick_SL_SMA,                           sd->spamcount_SL_SMA,                           battle_config.kd_SL_SMA,                           battle_config.kdw_SL_SMA))                           { sd->spamcount_SL_SMA = sd->k_tick_c; return 0; }                           sd->spamcount_SL_SMA = 0;                           sd->spamtick_SL_SMA = tick + sd->kdelay;                           break;
			case SL_SWOO:                          if (k_tick_check(sd, sd->spamtick_SL_SWOO,                          sd->spamcount_SL_SWOO,                          battle_config.kd_SL_SWOO,                          battle_config.kdw_SL_SWOO))                          { sd->spamcount_SL_SWOO = sd->k_tick_c; return 0; }                          sd->spamcount_SL_SWOO = 0;                          sd->spamtick_SL_SWOO = tick + sd->kdelay;                          break;
			case SL_SKE:                           if (k_tick_check(sd, sd->spamtick_SL_SKE,                           sd->spamcount_SL_SKE,                           battle_config.kd_SL_SKE,                           battle_config.kdw_SL_SKE))                           { sd->spamcount_SL_SKE = sd->k_tick_c; return 0; }                           sd->spamcount_SL_SKE = 0;                           sd->spamtick_SL_SKE = tick + sd->kdelay;                           break;
			case SL_SKA:                           if (k_tick_check(sd, sd->spamtick_SL_SKA,                           sd->spamcount_SL_SKA,                           battle_config.kd_SL_SKA,                           battle_config.kdw_SL_SKA))                           { sd->spamcount_SL_SKA = sd->k_tick_c; return 0; }                           sd->spamcount_SL_SKA = 0;                           sd->spamtick_SL_SKA = tick + sd->kdelay;                           break;
			case ST_FULLSTRIP:                     if (k_tick_check(sd, sd->spamtick_ST_FULLSTRIP,                     sd->spamcount_ST_FULLSTRIP,                     battle_config.kd_ST_FULLSTRIP,                     battle_config.kdw_ST_FULLSTRIP))                     { sd->spamcount_ST_FULLSTRIP = sd->k_tick_c; return 0; }                     sd->spamcount_ST_FULLSTRIP = 0;                     sd->spamtick_ST_FULLSTRIP = tick + sd->kdelay;                     break;
			case CR_SLIMPITCHER:                   if (k_tick_check(sd, sd->spamtick_CR_SLIMPITCHER,                   sd->spamcount_CR_SLIMPITCHER,                   battle_config.kd_CR_SLIMPITCHER,                   battle_config.kdw_CR_SLIMPITCHER))                   { sd->spamcount_CR_SLIMPITCHER = sd->k_tick_c; return 0; }                   sd->spamcount_CR_SLIMPITCHER = 0;                   sd->spamtick_CR_SLIMPITCHER = tick + sd->kdelay;                   break;
			case CR_FULLPROTECTION:                if (k_tick_check(sd, sd->spamtick_CR_FULLPROTECTION,                sd->spamcount_CR_FULLPROTECTION,                battle_config.kd_CR_FULLPROTECTION,                battle_config.kdw_CR_FULLPROTECTION))                { sd->spamcount_CR_FULLPROTECTION = sd->k_tick_c; return 0; }                sd->spamcount_CR_FULLPROTECTION = 0;                sd->spamtick_CR_FULLPROTECTION = tick + sd->kdelay;                break;
			case PA_SHIELDCHAIN:                   if (k_tick_check(sd, sd->spamtick_PA_SHIELDCHAIN,                   sd->spamcount_PA_SHIELDCHAIN,                   battle_config.kd_PA_SHIELDCHAIN,                   battle_config.kdw_PA_SHIELDCHAIN))                   { sd->spamcount_PA_SHIELDCHAIN = sd->k_tick_c; return 0; }                   sd->spamcount_PA_SHIELDCHAIN = 0;                   sd->spamtick_PA_SHIELDCHAIN = tick + sd->kdelay;                   break;
			case HP_MANARECHARGE:                  if (k_tick_check(sd, sd->spamtick_HP_MANARECHARGE,                  sd->spamcount_HP_MANARECHARGE,                  battle_config.kd_HP_MANARECHARGE,                  battle_config.kdw_HP_MANARECHARGE))                  { sd->spamcount_HP_MANARECHARGE = sd->k_tick_c; return 0; }                  sd->spamcount_HP_MANARECHARGE = 0;                  sd->spamtick_HP_MANARECHARGE = tick + sd->kdelay;                  break;
			case PF_DOUBLECASTING:                 if (k_tick_check(sd, sd->spamtick_PF_DOUBLECASTING,                 sd->spamcount_PF_DOUBLECASTING,                 battle_config.kd_PF_DOUBLECASTING,                 battle_config.kdw_PF_DOUBLECASTING))                 { sd->spamcount_PF_DOUBLECASTING = sd->k_tick_c; return 0; }                 sd->spamcount_PF_DOUBLECASTING = 0;                 sd->spamtick_PF_DOUBLECASTING = tick + sd->kdelay;                 break;
			case HW_GANBANTEIN:                    if (k_tick_check(sd, sd->spamtick_HW_GANBANTEIN,                    sd->spamcount_HW_GANBANTEIN,                    battle_config.kd_HW_GANBANTEIN,                    battle_config.kdw_HW_GANBANTEIN))                    { sd->spamcount_HW_GANBANTEIN = sd->k_tick_c; return 0; }                    sd->spamcount_HW_GANBANTEIN = 0;                    sd->spamtick_HW_GANBANTEIN = tick + sd->kdelay;                    break;
			case HW_GRAVITATION:                   if (k_tick_check(sd, sd->spamtick_HW_GRAVITATION,                   sd->spamcount_HW_GRAVITATION,                   battle_config.kd_HW_GRAVITATION,                   battle_config.kdw_HW_GRAVITATION))                   { sd->spamcount_HW_GRAVITATION = sd->k_tick_c; return 0; }                   sd->spamcount_HW_GRAVITATION = 0;                   sd->spamtick_HW_GRAVITATION = tick + sd->kdelay;                   break;
			case WS_CARTTERMINATION:               if (k_tick_check(sd, sd->spamtick_WS_CARTTERMINATION,               sd->spamcount_WS_CARTTERMINATION,               battle_config.kd_WS_CARTTERMINATION,               battle_config.kdw_WS_CARTTERMINATION))               { sd->spamcount_WS_CARTTERMINATION = sd->k_tick_c; return 0; }               sd->spamcount_WS_CARTTERMINATION = 0;               sd->spamtick_WS_CARTTERMINATION = tick + sd->kdelay;               break;
			case CG_HERMODE:                       if (k_tick_check(sd, sd->spamtick_CG_HERMODE,                       sd->spamcount_CG_HERMODE,                       battle_config.kd_CG_HERMODE,                       battle_config.kdw_CG_HERMODE))                       { sd->spamcount_CG_HERMODE = sd->k_tick_c; return 0; }                       sd->spamcount_CG_HERMODE = 0;                       sd->spamtick_CG_HERMODE = tick + sd->kdelay;                       break;
			case CG_TAROTCARD:                     if (k_tick_check(sd, sd->spamtick_CG_TAROTCARD,                     sd->spamcount_CG_TAROTCARD,                     battle_config.kd_CG_TAROTCARD,                     battle_config.kdw_CG_TAROTCARD))                     { sd->spamcount_CG_TAROTCARD = sd->k_tick_c; return 0; }                     sd->spamcount_CG_TAROTCARD = 0;                     sd->spamtick_CG_TAROTCARD = tick + sd->kdelay;                     break;
			case CR_ACIDDEMONSTRATION:             if (k_tick_check(sd, sd->spamtick_CR_ACIDDEMONSTRATION,             sd->spamcount_CR_ACIDDEMONSTRATION,             battle_config.kd_CR_ACIDDEMONSTRATION,             battle_config.kdw_CR_ACIDDEMONSTRATION))             { sd->spamcount_CR_ACIDDEMONSTRATION = sd->k_tick_c; return 0; }             sd->spamcount_CR_ACIDDEMONSTRATION = 0;             sd->spamtick_CR_ACIDDEMONSTRATION = tick + sd->kdelay;             break;
			case SL_HIGH:                          if (k_tick_check(sd, sd->spamtick_SL_HIGH,                          sd->spamcount_SL_HIGH,                          battle_config.kd_SL_HIGH,                          battle_config.kdw_SL_HIGH))                          { sd->spamcount_SL_HIGH = sd->k_tick_c; return 0; }                          sd->spamcount_SL_HIGH = 0;                          sd->spamtick_SL_HIGH = tick + sd->kdelay;                          break;
			case GS_TRIPLEACTION:                  if (k_tick_check(sd, sd->spamtick_GS_TRIPLEACTION,                  sd->spamcount_GS_TRIPLEACTION,                  battle_config.kd_GS_TRIPLEACTION,                  battle_config.kdw_GS_TRIPLEACTION))                  { sd->spamcount_GS_TRIPLEACTION = sd->k_tick_c; return 0; }                  sd->spamcount_GS_TRIPLEACTION = 0;                  sd->spamtick_GS_TRIPLEACTION = tick + sd->kdelay;                  break;
			case GS_BULLSEYE:                      if (k_tick_check(sd, sd->spamtick_GS_BULLSEYE,                      sd->spamcount_GS_BULLSEYE,                      battle_config.kd_GS_BULLSEYE,                      battle_config.kdw_GS_BULLSEYE))                      { sd->spamcount_GS_BULLSEYE = sd->k_tick_c; return 0; }                      sd->spamcount_GS_BULLSEYE = 0;                      sd->spamtick_GS_BULLSEYE = tick + sd->kdelay;                      break;
			case GS_MADNESSCANCEL:                 if (k_tick_check(sd, sd->spamtick_GS_MADNESSCANCEL,                 sd->spamcount_GS_MADNESSCANCEL,                 battle_config.kd_GS_MADNESSCANCEL,                 battle_config.kdw_GS_MADNESSCANCEL))                 { sd->spamcount_GS_MADNESSCANCEL = sd->k_tick_c; return 0; }                 sd->spamcount_GS_MADNESSCANCEL = 0;                 sd->spamtick_GS_MADNESSCANCEL = tick + sd->kdelay;                 break;
			case GS_INCREASING:                    if (k_tick_check(sd, sd->spamtick_GS_INCREASING,                    sd->spamcount_GS_INCREASING,                    battle_config.kd_GS_INCREASING,                    battle_config.kdw_GS_INCREASING))                    { sd->spamcount_GS_INCREASING = sd->k_tick_c; return 0; }                    sd->spamcount_GS_INCREASING = 0;                    sd->spamtick_GS_INCREASING = tick + sd->kdelay;                    break;
			case GS_MAGICALBULLET:                 if (k_tick_check(sd, sd->spamtick_GS_MAGICALBULLET,                 sd->spamcount_GS_MAGICALBULLET,                 battle_config.kd_GS_MAGICALBULLET,                 battle_config.kdw_GS_MAGICALBULLET))                 { sd->spamcount_GS_MAGICALBULLET = sd->k_tick_c; return 0; }                 sd->spamcount_GS_MAGICALBULLET = 0;                 sd->spamtick_GS_MAGICALBULLET = tick + sd->kdelay;                 break;
			case GS_CRACKER:                       if (k_tick_check(sd, sd->spamtick_GS_CRACKER,                       sd->spamcount_GS_CRACKER,                       battle_config.kd_GS_CRACKER,                       battle_config.kdw_GS_CRACKER))                       { sd->spamcount_GS_CRACKER = sd->k_tick_c; return 0; }                       sd->spamcount_GS_CRACKER = 0;                       sd->spamtick_GS_CRACKER = tick + sd->kdelay;                       break;
			case GS_SINGLEACTION:                  if (k_tick_check(sd, sd->spamtick_GS_SINGLEACTION,                  sd->spamcount_GS_SINGLEACTION,                  battle_config.kd_GS_SINGLEACTION,                  battle_config.kdw_GS_SINGLEACTION))                  { sd->spamcount_GS_SINGLEACTION = sd->k_tick_c; return 0; }                  sd->spamcount_GS_SINGLEACTION = 0;                  sd->spamtick_GS_SINGLEACTION = tick + sd->kdelay;                  break;
			case GS_CHAINACTION:                   if (k_tick_check(sd, sd->spamtick_GS_CHAINACTION,                   sd->spamcount_GS_CHAINACTION,                   battle_config.kd_GS_CHAINACTION,                   battle_config.kdw_GS_CHAINACTION))                   { sd->spamcount_GS_CHAINACTION = sd->k_tick_c; return 0; }                   sd->spamcount_GS_CHAINACTION = 0;                   sd->spamtick_GS_CHAINACTION = tick + sd->kdelay;                   break;
			case GS_TRACKING:                      if (k_tick_check(sd, sd->spamtick_GS_TRACKING,                      sd->spamcount_GS_TRACKING,                      battle_config.kd_GS_TRACKING,                      battle_config.kdw_GS_TRACKING))                      { sd->spamcount_GS_TRACKING = sd->k_tick_c; return 0; }                      sd->spamcount_GS_TRACKING = 0;                      sd->spamtick_GS_TRACKING = tick + sd->kdelay;                      break;
			case GS_DISARM:                        if (k_tick_check(sd, sd->spamtick_GS_DISARM,                        sd->spamcount_GS_DISARM,                        battle_config.kd_GS_DISARM,                        battle_config.kdw_GS_DISARM))                        { sd->spamcount_GS_DISARM = sd->k_tick_c; return 0; }                        sd->spamcount_GS_DISARM = 0;                        sd->spamtick_GS_DISARM = tick + sd->kdelay;                        break;
			case GS_PIERCINGSHOT:                  if (k_tick_check(sd, sd->spamtick_GS_PIERCINGSHOT,                  sd->spamcount_GS_PIERCINGSHOT,                  battle_config.kd_GS_PIERCINGSHOT,                  battle_config.kdw_GS_PIERCINGSHOT))                  { sd->spamcount_GS_PIERCINGSHOT = sd->k_tick_c; return 0; }                  sd->spamcount_GS_PIERCINGSHOT = 0;                  sd->spamtick_GS_PIERCINGSHOT = tick + sd->kdelay;                  break;
			case GS_RAPIDSHOWER:                   if (k_tick_check(sd, sd->spamtick_GS_RAPIDSHOWER,                   sd->spamcount_GS_RAPIDSHOWER,                   battle_config.kd_GS_RAPIDSHOWER,                   battle_config.kdw_GS_RAPIDSHOWER))                   { sd->spamcount_GS_RAPIDSHOWER = sd->k_tick_c; return 0; }                   sd->spamcount_GS_RAPIDSHOWER = 0;                   sd->spamtick_GS_RAPIDSHOWER = tick + sd->kdelay;                   break;
			case GS_DESPERADO:                     if (k_tick_check(sd, sd->spamtick_GS_DESPERADO,                     sd->spamcount_GS_DESPERADO,                     battle_config.kd_GS_DESPERADO,                     battle_config.kdw_GS_DESPERADO))                     { sd->spamcount_GS_DESPERADO = sd->k_tick_c; return 0; }                     sd->spamcount_GS_DESPERADO = 0;                     sd->spamtick_GS_DESPERADO = tick + sd->kdelay;                     break;
			case GS_GATLINGFEVER:                  if (k_tick_check(sd, sd->spamtick_GS_GATLINGFEVER,                  sd->spamcount_GS_GATLINGFEVER,                  battle_config.kd_GS_GATLINGFEVER,                  battle_config.kdw_GS_GATLINGFEVER))                  { sd->spamcount_GS_GATLINGFEVER = sd->k_tick_c; return 0; }                  sd->spamcount_GS_GATLINGFEVER = 0;                  sd->spamtick_GS_GATLINGFEVER = tick + sd->kdelay;                  break;
			case GS_DUST:                          if (k_tick_check(sd, sd->spamtick_GS_DUST,                          sd->spamcount_GS_DUST,                          battle_config.kd_GS_DUST,                          battle_config.kdw_GS_DUST))                          { sd->spamcount_GS_DUST = sd->k_tick_c; return 0; }                          sd->spamcount_GS_DUST = 0;                          sd->spamtick_GS_DUST = tick + sd->kdelay;                          break;
			case GS_FULLBUSTER:                    if (k_tick_check(sd, sd->spamtick_GS_FULLBUSTER,                    sd->spamcount_GS_FULLBUSTER,                    battle_config.kd_GS_FULLBUSTER,                    battle_config.kdw_GS_FULLBUSTER))                    { sd->spamcount_GS_FULLBUSTER = sd->k_tick_c; return 0; }                    sd->spamcount_GS_FULLBUSTER = 0;                    sd->spamtick_GS_FULLBUSTER = tick + sd->kdelay;                    break;
			case GS_SPREADATTACK:                  if (k_tick_check(sd, sd->spamtick_GS_SPREADATTACK,                  sd->spamcount_GS_SPREADATTACK,                  battle_config.kd_GS_SPREADATTACK,                  battle_config.kdw_GS_SPREADATTACK))                  { sd->spamcount_GS_SPREADATTACK = sd->k_tick_c; return 0; }                  sd->spamcount_GS_SPREADATTACK = 0;                  sd->spamtick_GS_SPREADATTACK = tick + sd->kdelay;                  break;
			case GS_GROUNDDRIFT:                   if (k_tick_check(sd, sd->spamtick_GS_GROUNDDRIFT,                   sd->spamcount_GS_GROUNDDRIFT,                   battle_config.kd_GS_GROUNDDRIFT,                   battle_config.kdw_GS_GROUNDDRIFT))                   { sd->spamcount_GS_GROUNDDRIFT = sd->k_tick_c; return 0; }                   sd->spamcount_GS_GROUNDDRIFT = 0;                   sd->spamtick_GS_GROUNDDRIFT = tick + sd->kdelay;                   break;
			case NJ_TOBIDOUGU:                     if (k_tick_check(sd, sd->spamtick_NJ_TOBIDOUGU,                     sd->spamcount_NJ_TOBIDOUGU,                     battle_config.kd_NJ_TOBIDOUGU,                     battle_config.kdw_NJ_TOBIDOUGU))                     { sd->spamcount_NJ_TOBIDOUGU = sd->k_tick_c; return 0; }                     sd->spamcount_NJ_TOBIDOUGU = 0;                     sd->spamtick_NJ_TOBIDOUGU = tick + sd->kdelay;                     break;
			case NJ_SYURIKEN:                      if (k_tick_check(sd, sd->spamtick_NJ_SYURIKEN,                      sd->spamcount_NJ_SYURIKEN,                      battle_config.kd_NJ_SYURIKEN,                      battle_config.kdw_NJ_SYURIKEN))                      { sd->spamcount_NJ_SYURIKEN = sd->k_tick_c; return 0; }                      sd->spamcount_NJ_SYURIKEN = 0;                      sd->spamtick_NJ_SYURIKEN = tick + sd->kdelay;                      break;
			case NJ_KUNAI:                         if (k_tick_check(sd, sd->spamtick_NJ_KUNAI,                         sd->spamcount_NJ_KUNAI,                         battle_config.kd_NJ_KUNAI,                         battle_config.kdw_NJ_KUNAI))                         { sd->spamcount_NJ_KUNAI = sd->k_tick_c; return 0; }                         sd->spamcount_NJ_KUNAI = 0;                         sd->spamtick_NJ_KUNAI = tick + sd->kdelay;                         break;
			case NJ_HUUMA:                         if (k_tick_check(sd, sd->spamtick_NJ_HUUMA,                         sd->spamcount_NJ_HUUMA,                         battle_config.kd_NJ_HUUMA,                         battle_config.kdw_NJ_HUUMA))                         { sd->spamcount_NJ_HUUMA = sd->k_tick_c; return 0; }                         sd->spamcount_NJ_HUUMA = 0;                         sd->spamtick_NJ_HUUMA = tick + sd->kdelay;                         break;
			case NJ_ZENYNAGE:                      if (k_tick_check(sd, sd->spamtick_NJ_ZENYNAGE,                      sd->spamcount_NJ_ZENYNAGE,                      battle_config.kd_NJ_ZENYNAGE,                      battle_config.kdw_NJ_ZENYNAGE))                      { sd->spamcount_NJ_ZENYNAGE = sd->k_tick_c; return 0; }                      sd->spamcount_NJ_ZENYNAGE = 0;                      sd->spamtick_NJ_ZENYNAGE = tick + sd->kdelay;                      break;
			case NJ_TATAMIGAESHI:                  if (k_tick_check(sd, sd->spamtick_NJ_TATAMIGAESHI,                  sd->spamcount_NJ_TATAMIGAESHI,                  battle_config.kd_NJ_TATAMIGAESHI,                  battle_config.kdw_NJ_TATAMIGAESHI))                  { sd->spamcount_NJ_TATAMIGAESHI = sd->k_tick_c; return 0; }                  sd->spamcount_NJ_TATAMIGAESHI = 0;                  sd->spamtick_NJ_TATAMIGAESHI = tick + sd->kdelay;                  break;
			case NJ_KASUMIKIRI:                    if (k_tick_check(sd, sd->spamtick_NJ_KASUMIKIRI,                    sd->spamcount_NJ_KASUMIKIRI,                    battle_config.kd_NJ_KASUMIKIRI,                    battle_config.kdw_NJ_KASUMIKIRI))                    { sd->spamcount_NJ_KASUMIKIRI = sd->k_tick_c; return 0; }                    sd->spamcount_NJ_KASUMIKIRI = 0;                    sd->spamtick_NJ_KASUMIKIRI = tick + sd->kdelay;                    break;
			case NJ_SHADOWJUMP:                    if (k_tick_check(sd, sd->spamtick_NJ_SHADOWJUMP,                    sd->spamcount_NJ_SHADOWJUMP,                    battle_config.kd_NJ_SHADOWJUMP,                    battle_config.kdw_NJ_SHADOWJUMP))                    { sd->spamcount_NJ_SHADOWJUMP = sd->k_tick_c; return 0; }                    sd->spamcount_NJ_SHADOWJUMP = 0;                    sd->spamtick_NJ_SHADOWJUMP = tick + sd->kdelay;                    break;
			case NJ_KIRIKAGE:                      if (k_tick_check(sd, sd->spamtick_NJ_KIRIKAGE,                      sd->spamcount_NJ_KIRIKAGE,                      battle_config.kd_NJ_KIRIKAGE,                      battle_config.kdw_NJ_KIRIKAGE))                      { sd->spamcount_NJ_KIRIKAGE = sd->k_tick_c; return 0; }                      sd->spamcount_NJ_KIRIKAGE = 0;                      sd->spamtick_NJ_KIRIKAGE = tick + sd->kdelay;                      break;
			case NJ_UTSUSEMI:                      if (k_tick_check(sd, sd->spamtick_NJ_UTSUSEMI,                      sd->spamcount_NJ_UTSUSEMI,                      battle_config.kd_NJ_UTSUSEMI,                      battle_config.kdw_NJ_UTSUSEMI))                      { sd->spamcount_NJ_UTSUSEMI = sd->k_tick_c; return 0; }                      sd->spamcount_NJ_UTSUSEMI = 0;                      sd->spamtick_NJ_UTSUSEMI = tick + sd->kdelay;                      break;
			case NJ_BUNSINJYUTSU:                  if (k_tick_check(sd, sd->spamtick_NJ_BUNSINJYUTSU,                  sd->spamcount_NJ_BUNSINJYUTSU,                  battle_config.kd_NJ_BUNSINJYUTSU,                  battle_config.kdw_NJ_BUNSINJYUTSU))                  { sd->spamcount_NJ_BUNSINJYUTSU = sd->k_tick_c; return 0; }                  sd->spamcount_NJ_BUNSINJYUTSU = 0;                  sd->spamtick_NJ_BUNSINJYUTSU = tick + sd->kdelay;                  break;
			case NJ_NINPOU:                        if (k_tick_check(sd, sd->spamtick_NJ_NINPOU,                        sd->spamcount_NJ_NINPOU,                        battle_config.kd_NJ_NINPOU,                        battle_config.kdw_NJ_NINPOU))                        { sd->spamcount_NJ_NINPOU = sd->k_tick_c; return 0; }                        sd->spamcount_NJ_NINPOU = 0;                        sd->spamtick_NJ_NINPOU = tick + sd->kdelay;                        break;
			case NJ_KOUENKA:                       if (k_tick_check(sd, sd->spamtick_NJ_KOUENKA,                       sd->spamcount_NJ_KOUENKA,                       battle_config.kd_NJ_KOUENKA,                       battle_config.kdw_NJ_KOUENKA))                       { sd->spamcount_NJ_KOUENKA = sd->k_tick_c; return 0; }                       sd->spamcount_NJ_KOUENKA = 0;                       sd->spamtick_NJ_KOUENKA = tick + sd->kdelay;                       break;
			case NJ_KAENSIN:                       if (k_tick_check(sd, sd->spamtick_NJ_KAENSIN,                       sd->spamcount_NJ_KAENSIN,                       battle_config.kd_NJ_KAENSIN,                       battle_config.kdw_NJ_KAENSIN))                       { sd->spamcount_NJ_KAENSIN = sd->k_tick_c; return 0; }                       sd->spamcount_NJ_KAENSIN = 0;                       sd->spamtick_NJ_KAENSIN = tick + sd->kdelay;                       break;
			case NJ_BAKUENRYU:                     if (k_tick_check(sd, sd->spamtick_NJ_BAKUENRYU,                     sd->spamcount_NJ_BAKUENRYU,                     battle_config.kd_NJ_BAKUENRYU,                     battle_config.kdw_NJ_BAKUENRYU))                     { sd->spamcount_NJ_BAKUENRYU = sd->k_tick_c; return 0; }                     sd->spamcount_NJ_BAKUENRYU = 0;                     sd->spamtick_NJ_BAKUENRYU = tick + sd->kdelay;                     break;
			case NJ_HYOUSENSOU:                    if (k_tick_check(sd, sd->spamtick_NJ_HYOUSENSOU,                    sd->spamcount_NJ_HYOUSENSOU,                    battle_config.kd_NJ_HYOUSENSOU,                    battle_config.kdw_NJ_HYOUSENSOU))                    { sd->spamcount_NJ_HYOUSENSOU = sd->k_tick_c; return 0; }                    sd->spamcount_NJ_HYOUSENSOU = 0;                    sd->spamtick_NJ_HYOUSENSOU = tick + sd->kdelay;                    break;
			case NJ_SUITON:                        if (k_tick_check(sd, sd->spamtick_NJ_SUITON,                        sd->spamcount_NJ_SUITON,                        battle_config.kd_NJ_SUITON,                        battle_config.kdw_NJ_SUITON))                        { sd->spamcount_NJ_SUITON = sd->k_tick_c; return 0; }                        sd->spamcount_NJ_SUITON = 0;                        sd->spamtick_NJ_SUITON = tick + sd->kdelay;                        break;
			case NJ_HYOUSYOURAKU:                  if (k_tick_check(sd, sd->spamtick_NJ_HYOUSYOURAKU,                  sd->spamcount_NJ_HYOUSYOURAKU,                  battle_config.kd_NJ_HYOUSYOURAKU,                  battle_config.kdw_NJ_HYOUSYOURAKU))                  { sd->spamcount_NJ_HYOUSYOURAKU = sd->k_tick_c; return 0; }                  sd->spamcount_NJ_HYOUSYOURAKU = 0;                  sd->spamtick_NJ_HYOUSYOURAKU = tick + sd->kdelay;                  break;
			case NJ_HUUJIN:                        if (k_tick_check(sd, sd->spamtick_NJ_HUUJIN,                        sd->spamcount_NJ_HUUJIN,                        battle_config.kd_NJ_HUUJIN,                        battle_config.kdw_NJ_HUUJIN))                        { sd->spamcount_NJ_HUUJIN = sd->k_tick_c; return 0; }                        sd->spamcount_NJ_HUUJIN = 0;                        sd->spamtick_NJ_HUUJIN = tick + sd->kdelay;                        break;
			case NJ_RAIGEKISAI:                    if (k_tick_check(sd, sd->spamtick_NJ_RAIGEKISAI,                    sd->spamcount_NJ_RAIGEKISAI,                    battle_config.kd_NJ_RAIGEKISAI,                    battle_config.kdw_NJ_RAIGEKISAI))                    { sd->spamcount_NJ_RAIGEKISAI = sd->k_tick_c; return 0; }                    sd->spamcount_NJ_RAIGEKISAI = 0;                    sd->spamtick_NJ_RAIGEKISAI = tick + sd->kdelay;                    break;
			case NJ_KAMAITACHI:                    if (k_tick_check(sd, sd->spamtick_NJ_KAMAITACHI,                    sd->spamcount_NJ_KAMAITACHI,                    battle_config.kd_NJ_KAMAITACHI,                    battle_config.kdw_NJ_KAMAITACHI))                    { sd->spamcount_NJ_KAMAITACHI = sd->k_tick_c; return 0; }                    sd->spamcount_NJ_KAMAITACHI = 0;                    sd->spamtick_NJ_KAMAITACHI = tick + sd->kdelay;                    break;
			case NJ_NEN:                           if (k_tick_check(sd, sd->spamtick_NJ_NEN,                           sd->spamcount_NJ_NEN,                           battle_config.kd_NJ_NEN,                           battle_config.kdw_NJ_NEN))                           { sd->spamcount_NJ_NEN = sd->k_tick_c; return 0; }                           sd->spamcount_NJ_NEN = 0;                           sd->spamtick_NJ_NEN = tick + sd->kdelay;                           break;
			case NJ_ISSEN:                         if (k_tick_check(sd, sd->spamtick_NJ_ISSEN,                         sd->spamcount_NJ_ISSEN,                         battle_config.kd_NJ_ISSEN,                         battle_config.kdw_NJ_ISSEN))                         { sd->spamcount_NJ_ISSEN = sd->k_tick_c; return 0; }                         sd->spamcount_NJ_ISSEN = 0;                         sd->spamtick_NJ_ISSEN = tick + sd->kdelay;                         break;
			case KN_CHARGEATK:                     if (k_tick_check(sd, sd->spamtick_KN_CHARGEATK,                     sd->spamcount_KN_CHARGEATK,                     battle_config.kd_KN_CHARGEATK,                     battle_config.kdw_KN_CHARGEATK))                     { sd->spamcount_KN_CHARGEATK = sd->k_tick_c; return 0; }                     sd->spamcount_KN_CHARGEATK = 0;                     sd->spamtick_KN_CHARGEATK = tick + sd->kdelay;                     break;
			case AS_VENOMKNIFE:                    if (k_tick_check(sd, sd->spamtick_AS_VENOMKNIFE,                    sd->spamcount_AS_VENOMKNIFE,                    battle_config.kd_AS_VENOMKNIFE,                    battle_config.kdw_AS_VENOMKNIFE))                    { sd->spamcount_AS_VENOMKNIFE = sd->k_tick_c; return 0; }                    sd->spamcount_AS_VENOMKNIFE = 0;                    sd->spamtick_AS_VENOMKNIFE = tick + sd->kdelay;                    break;
			case RG_CLOSECONFINE:                  if (k_tick_check(sd, sd->spamtick_RG_CLOSECONFINE,                  sd->spamcount_RG_CLOSECONFINE,                  battle_config.kd_RG_CLOSECONFINE,                  battle_config.kdw_RG_CLOSECONFINE))                  { sd->spamcount_RG_CLOSECONFINE = sd->k_tick_c; return 0; }                  sd->spamcount_RG_CLOSECONFINE = 0;                  sd->spamtick_RG_CLOSECONFINE = tick + sd->kdelay;                  break;
			case WZ_SIGHTBLASTER:                  if (k_tick_check(sd, sd->spamtick_WZ_SIGHTBLASTER,                  sd->spamcount_WZ_SIGHTBLASTER,                  battle_config.kd_WZ_SIGHTBLASTER,                  battle_config.kdw_WZ_SIGHTBLASTER))                  { sd->spamcount_WZ_SIGHTBLASTER = sd->k_tick_c; return 0; }                  sd->spamcount_WZ_SIGHTBLASTER = 0;                  sd->spamtick_WZ_SIGHTBLASTER = tick + sd->kdelay;                  break;
			case HT_PHANTASMIC:                    if (k_tick_check(sd, sd->spamtick_HT_PHANTASMIC,                    sd->spamcount_HT_PHANTASMIC,                    battle_config.kd_HT_PHANTASMIC,                    battle_config.kdw_HT_PHANTASMIC))                    { sd->spamcount_HT_PHANTASMIC = sd->k_tick_c; return 0; }                    sd->spamcount_HT_PHANTASMIC = 0;                    sd->spamtick_HT_PHANTASMIC = tick + sd->kdelay;                    break;
			case BA_PANGVOICE:                     if (k_tick_check(sd, sd->spamtick_BA_PANGVOICE,                     sd->spamcount_BA_PANGVOICE,                     battle_config.kd_BA_PANGVOICE,                     battle_config.kdw_BA_PANGVOICE))                     { sd->spamcount_BA_PANGVOICE = sd->k_tick_c; return 0; }                     sd->spamcount_BA_PANGVOICE = 0;                     sd->spamtick_BA_PANGVOICE = tick + sd->kdelay;                     break;
			case DC_WINKCHARM:                     if (k_tick_check(sd, sd->spamtick_DC_WINKCHARM,                     sd->spamcount_DC_WINKCHARM,                     battle_config.kd_DC_WINKCHARM,                     battle_config.kdw_DC_WINKCHARM))                     { sd->spamcount_DC_WINKCHARM = sd->k_tick_c; return 0; }                     sd->spamcount_DC_WINKCHARM = 0;                     sd->spamtick_DC_WINKCHARM = tick + sd->kdelay;                     break;
			case PR_REDEMPTIO:                     if (k_tick_check(sd, sd->spamtick_PR_REDEMPTIO,                     sd->spamcount_PR_REDEMPTIO,                     battle_config.kd_PR_REDEMPTIO,                     battle_config.kdw_PR_REDEMPTIO))                     { sd->spamcount_PR_REDEMPTIO = sd->k_tick_c; return 0; }                     sd->spamcount_PR_REDEMPTIO = 0;                     sd->spamtick_PR_REDEMPTIO = tick + sd->kdelay;                     break;
			case MO_KITRANSLATION:                 if (k_tick_check(sd, sd->spamtick_MO_KITRANSLATION,                 sd->spamcount_MO_KITRANSLATION,                 battle_config.kd_MO_KITRANSLATION,                 battle_config.kdw_MO_KITRANSLATION))                 { sd->spamcount_MO_KITRANSLATION = sd->k_tick_c; return 0; }                 sd->spamcount_MO_KITRANSLATION = 0;                 sd->spamtick_MO_KITRANSLATION = tick + sd->kdelay;                 break;
			case MO_BALKYOUNG:                     if (k_tick_check(sd, sd->spamtick_MO_BALKYOUNG,                     sd->spamcount_MO_BALKYOUNG,                     battle_config.kd_MO_BALKYOUNG,                     battle_config.kdw_MO_BALKYOUNG))                     { sd->spamcount_MO_BALKYOUNG = sd->k_tick_c; return 0; }                     sd->spamcount_MO_BALKYOUNG = 0;                     sd->spamtick_MO_BALKYOUNG = tick + sd->kdelay;                     break;
			case RK_SONICWAVE:                     if (k_tick_check(sd, sd->spamtick_RK_SONICWAVE,                     sd->spamcount_RK_SONICWAVE,                     battle_config.kd_RK_SONICWAVE,                     battle_config.kdw_RK_SONICWAVE))                     { sd->spamcount_RK_SONICWAVE = sd->k_tick_c; return 0; }                     sd->spamcount_RK_SONICWAVE = 0;                     sd->spamtick_RK_SONICWAVE = tick + sd->kdelay;                     break;
			case RK_DEATHBOUND:                    if (k_tick_check(sd, sd->spamtick_RK_DEATHBOUND,                    sd->spamcount_RK_DEATHBOUND,                    battle_config.kd_RK_DEATHBOUND,                    battle_config.kdw_RK_DEATHBOUND))                    { sd->spamcount_RK_DEATHBOUND = sd->k_tick_c; return 0; }                    sd->spamcount_RK_DEATHBOUND = 0;                    sd->spamtick_RK_DEATHBOUND = tick + sd->kdelay;                    break;
			case RK_HUNDREDSPEAR:                  if (k_tick_check(sd, sd->spamtick_RK_HUNDREDSPEAR,                  sd->spamcount_RK_HUNDREDSPEAR,                  battle_config.kd_RK_HUNDREDSPEAR,                  battle_config.kdw_RK_HUNDREDSPEAR))                  { sd->spamcount_RK_HUNDREDSPEAR = sd->k_tick_c; return 0; }                  sd->spamcount_RK_HUNDREDSPEAR = 0;                  sd->spamtick_RK_HUNDREDSPEAR = tick + sd->kdelay;                  break;
			case RK_WINDCUTTER:                    if (k_tick_check(sd, sd->spamtick_RK_WINDCUTTER,                    sd->spamcount_RK_WINDCUTTER,                    battle_config.kd_RK_WINDCUTTER,                    battle_config.kdw_RK_WINDCUTTER))                    { sd->spamcount_RK_WINDCUTTER = sd->k_tick_c; return 0; }                    sd->spamcount_RK_WINDCUTTER = 0;                    sd->spamtick_RK_WINDCUTTER = tick + sd->kdelay;                    break;
			case RK_IGNITIONBREAK:                 if (k_tick_check(sd, sd->spamtick_RK_IGNITIONBREAK,                 sd->spamcount_RK_IGNITIONBREAK,                 battle_config.kd_RK_IGNITIONBREAK,                 battle_config.kdw_RK_IGNITIONBREAK))                 { sd->spamcount_RK_IGNITIONBREAK = sd->k_tick_c; return 0; }                 sd->spamcount_RK_IGNITIONBREAK = 0;                 sd->spamtick_RK_IGNITIONBREAK = tick + sd->kdelay;                 break;
			case RK_DRAGONBREATH:                  if (k_tick_check(sd, sd->spamtick_RK_DRAGONBREATH,                  sd->spamcount_RK_DRAGONBREATH,                  battle_config.kd_RK_DRAGONBREATH,                  battle_config.kdw_RK_DRAGONBREATH))                  { sd->spamcount_RK_DRAGONBREATH = sd->k_tick_c; return 0; }                  sd->spamcount_RK_DRAGONBREATH = 0;                  sd->spamtick_RK_DRAGONBREATH = tick + sd->kdelay;                  break;
			case RK_CRUSHSTRIKE:                   if (k_tick_check(sd, sd->spamtick_RK_CRUSHSTRIKE,                   sd->spamcount_RK_CRUSHSTRIKE,                   battle_config.kd_RK_CRUSHSTRIKE,                   battle_config.kdw_RK_CRUSHSTRIKE))                   { sd->spamcount_RK_CRUSHSTRIKE = sd->k_tick_c; return 0; }                   sd->spamcount_RK_CRUSHSTRIKE = 0;                   sd->spamtick_RK_CRUSHSTRIKE = tick + sd->kdelay;                   break;
			case RK_STORMBLAST:                    if (k_tick_check(sd, sd->spamtick_RK_STORMBLAST,                    sd->spamcount_RK_STORMBLAST,                    battle_config.kd_RK_STORMBLAST,                    battle_config.kdw_RK_STORMBLAST))                    { sd->spamcount_RK_STORMBLAST = sd->k_tick_c; return 0; }                    sd->spamcount_RK_STORMBLAST = 0;                    sd->spamtick_RK_STORMBLAST = tick + sd->kdelay;                    break;
			case RK_PHANTOMTHRUST:                 if (k_tick_check(sd, sd->spamtick_RK_PHANTOMTHRUST,                 sd->spamcount_RK_PHANTOMTHRUST,                 battle_config.kd_RK_PHANTOMTHRUST,                 battle_config.kdw_RK_PHANTOMTHRUST))                 { sd->spamcount_RK_PHANTOMTHRUST = sd->k_tick_c; return 0; }                 sd->spamcount_RK_PHANTOMTHRUST = 0;                 sd->spamtick_RK_PHANTOMTHRUST = tick + sd->kdelay;                 break;
			case GC_CROSSIMPACT:                   if (k_tick_check(sd, sd->spamtick_GC_CROSSIMPACT,                   sd->spamcount_GC_CROSSIMPACT,                   battle_config.kd_GC_CROSSIMPACT,                   battle_config.kdw_GC_CROSSIMPACT))                   { sd->spamcount_GC_CROSSIMPACT = sd->k_tick_c; return 0; }                   sd->spamcount_GC_CROSSIMPACT = 0;                   sd->spamtick_GC_CROSSIMPACT = tick + sd->kdelay;                   break;
			case GC_WEAPONCRUSH:                   if (k_tick_check(sd, sd->spamtick_GC_WEAPONCRUSH,                   sd->spamcount_GC_WEAPONCRUSH,                   battle_config.kd_GC_WEAPONCRUSH,                   battle_config.kdw_GC_WEAPONCRUSH))                   { sd->spamcount_GC_WEAPONCRUSH = sd->k_tick_c; return 0; }                   sd->spamcount_GC_WEAPONCRUSH = 0;                   sd->spamtick_GC_WEAPONCRUSH = tick + sd->kdelay;                   break;
			case GC_ROLLINGCUTTER:                 if (k_tick_check(sd, sd->spamtick_GC_ROLLINGCUTTER,                 sd->spamcount_GC_ROLLINGCUTTER,                 battle_config.kd_GC_ROLLINGCUTTER,                 battle_config.kdw_GC_ROLLINGCUTTER))                 { sd->spamcount_GC_ROLLINGCUTTER = sd->k_tick_c; return 0; }                 sd->spamcount_GC_ROLLINGCUTTER = 0;                 sd->spamtick_GC_ROLLINGCUTTER = tick + sd->kdelay;                 break;
			case GC_CROSSRIPPERSLASHER:            if (k_tick_check(sd, sd->spamtick_GC_CROSSRIPPERSLASHER,            sd->spamcount_GC_CROSSRIPPERSLASHER,            battle_config.kd_GC_CROSSRIPPERSLASHER,            battle_config.kdw_GC_CROSSRIPPERSLASHER))            { sd->spamcount_GC_CROSSRIPPERSLASHER = sd->k_tick_c; return 0; }            sd->spamcount_GC_CROSSRIPPERSLASHER = 0;            sd->spamtick_GC_CROSSRIPPERSLASHER = tick + sd->kdelay;            break;
			case AB_JUDEX:                         if (k_tick_check(sd, sd->spamtick_AB_JUDEX,                         sd->spamcount_AB_JUDEX,                         battle_config.kd_AB_JUDEX,                         battle_config.kdw_AB_JUDEX))                         { sd->spamcount_AB_JUDEX = sd->k_tick_c; return 0; }                         sd->spamcount_AB_JUDEX = 0;                         sd->spamtick_AB_JUDEX = tick + sd->kdelay;                         break;
			case AB_ADORAMUS:                      if (k_tick_check(sd, sd->spamtick_AB_ADORAMUS,                      sd->spamcount_AB_ADORAMUS,                      battle_config.kd_AB_ADORAMUS,                      battle_config.kdw_AB_ADORAMUS))                      { sd->spamcount_AB_ADORAMUS = sd->k_tick_c; return 0; }                      sd->spamcount_AB_ADORAMUS = 0;                      sd->spamtick_AB_ADORAMUS = tick + sd->kdelay;                      break;
			case AB_CHEAL:                         if (k_tick_check(sd, sd->spamtick_AB_CHEAL,                         sd->spamcount_AB_CHEAL,                         battle_config.kd_AB_CHEAL,                         battle_config.kdw_AB_CHEAL))                         { sd->spamcount_AB_CHEAL = sd->k_tick_c; return 0; }                         sd->spamcount_AB_CHEAL = 0;                         sd->spamtick_AB_CHEAL = tick + sd->kdelay;                         break;
			case AB_EPICLESIS:                     if (k_tick_check(sd, sd->spamtick_AB_EPICLESIS,                     sd->spamcount_AB_EPICLESIS,                     battle_config.kd_AB_EPICLESIS,                     battle_config.kdw_AB_EPICLESIS))                     { sd->spamcount_AB_EPICLESIS = sd->k_tick_c; return 0; }                     sd->spamcount_AB_EPICLESIS = 0;                     sd->spamtick_AB_EPICLESIS = tick + sd->kdelay;                     break;
			case AB_PRAEFATIO:                     if (k_tick_check(sd, sd->spamtick_AB_PRAEFATIO,                     sd->spamcount_AB_PRAEFATIO,                     battle_config.kd_AB_PRAEFATIO,                     battle_config.kdw_AB_PRAEFATIO))                     { sd->spamcount_AB_PRAEFATIO = sd->k_tick_c; return 0; }                     sd->spamcount_AB_PRAEFATIO = 0;                     sd->spamtick_AB_PRAEFATIO = tick + sd->kdelay;                     break;
			case AB_EUCHARISTICA:                  if (k_tick_check(sd, sd->spamtick_AB_EUCHARISTICA,                  sd->spamcount_AB_EUCHARISTICA,                  battle_config.kd_AB_EUCHARISTICA,                  battle_config.kdw_AB_EUCHARISTICA))                  { sd->spamcount_AB_EUCHARISTICA = sd->k_tick_c; return 0; }                  sd->spamcount_AB_EUCHARISTICA = 0;                  sd->spamtick_AB_EUCHARISTICA = tick + sd->kdelay;                  break;
			case AB_RENOVATIO:                     if (k_tick_check(sd, sd->spamtick_AB_RENOVATIO,                     sd->spamcount_AB_RENOVATIO,                     battle_config.kd_AB_RENOVATIO,                     battle_config.kdw_AB_RENOVATIO))                     { sd->spamcount_AB_RENOVATIO = sd->k_tick_c; return 0; }                     sd->spamcount_AB_RENOVATIO = 0;                     sd->spamtick_AB_RENOVATIO = tick + sd->kdelay;                     break;
			case AB_HIGHNESSHEAL:                  if (k_tick_check(sd, sd->spamtick_AB_HIGHNESSHEAL,                  sd->spamcount_AB_HIGHNESSHEAL,                  battle_config.kd_AB_HIGHNESSHEAL,                  battle_config.kdw_AB_HIGHNESSHEAL))                  { sd->spamcount_AB_HIGHNESSHEAL = sd->k_tick_c; return 0; }                  sd->spamcount_AB_HIGHNESSHEAL = 0;                  sd->spamtick_AB_HIGHNESSHEAL = tick + sd->kdelay;                  break;
			case AB_CLEARANCE:                     if (k_tick_check(sd, sd->spamtick_AB_CLEARANCE,                     sd->spamcount_AB_CLEARANCE,                     battle_config.kd_AB_CLEARANCE,                     battle_config.kdw_AB_CLEARANCE))                     { sd->spamcount_AB_CLEARANCE = sd->k_tick_c; return 0; }                     sd->spamcount_AB_CLEARANCE = 0;                     sd->spamtick_AB_CLEARANCE = tick + sd->kdelay;                     break;
			case AB_EXPIATIO:                      if (k_tick_check(sd, sd->spamtick_AB_EXPIATIO,                      sd->spamcount_AB_EXPIATIO,                      battle_config.kd_AB_EXPIATIO,                      battle_config.kdw_AB_EXPIATIO))                      { sd->spamcount_AB_EXPIATIO = sd->k_tick_c; return 0; }                      sd->spamcount_AB_EXPIATIO = 0;                      sd->spamtick_AB_EXPIATIO = tick + sd->kdelay;                      break;
			case AB_DUPLELIGHT:                    if (k_tick_check(sd, sd->spamtick_AB_DUPLELIGHT,                    sd->spamcount_AB_DUPLELIGHT,                    battle_config.kd_AB_DUPLELIGHT,                    battle_config.kdw_AB_DUPLELIGHT))                    { sd->spamcount_AB_DUPLELIGHT = sd->k_tick_c; return 0; }                    sd->spamcount_AB_DUPLELIGHT = 0;                    sd->spamtick_AB_DUPLELIGHT = tick + sd->kdelay;                    break;
			case AB_DUPLELIGHT_MELEE:              if (k_tick_check(sd, sd->spamtick_AB_DUPLELIGHT_MELEE,              sd->spamcount_AB_DUPLELIGHT_MELEE,              battle_config.kd_AB_DUPLELIGHT_MELEE,              battle_config.kdw_AB_DUPLELIGHT_MELEE))              { sd->spamcount_AB_DUPLELIGHT_MELEE = sd->k_tick_c; return 0; }              sd->spamcount_AB_DUPLELIGHT_MELEE = 0;              sd->spamtick_AB_DUPLELIGHT_MELEE = tick + sd->kdelay;              break;
			case AB_DUPLELIGHT_MAGIC:              if (k_tick_check(sd, sd->spamtick_AB_DUPLELIGHT_MAGIC,              sd->spamcount_AB_DUPLELIGHT_MAGIC,              battle_config.kd_AB_DUPLELIGHT_MAGIC,              battle_config.kdw_AB_DUPLELIGHT_MAGIC))              { sd->spamcount_AB_DUPLELIGHT_MAGIC = sd->k_tick_c; return 0; }              sd->spamcount_AB_DUPLELIGHT_MAGIC = 0;              sd->spamtick_AB_DUPLELIGHT_MAGIC = tick + sd->kdelay;              break;
			case AB_SILENTIUM:                     if (k_tick_check(sd, sd->spamtick_AB_SILENTIUM,                     sd->spamcount_AB_SILENTIUM,                     battle_config.kd_AB_SILENTIUM,                     battle_config.kdw_AB_SILENTIUM))                     { sd->spamcount_AB_SILENTIUM = sd->k_tick_c; return 0; }                     sd->spamcount_AB_SILENTIUM = 0;                     sd->spamtick_AB_SILENTIUM = tick + sd->kdelay;                     break;
			case WL_WHITEIMPRISON:                 if (k_tick_check(sd, sd->spamtick_WL_WHITEIMPRISON,                 sd->spamcount_WL_WHITEIMPRISON,                 battle_config.kd_WL_WHITEIMPRISON,                 battle_config.kdw_WL_WHITEIMPRISON))                 { sd->spamcount_WL_WHITEIMPRISON = sd->k_tick_c; return 0; }                 sd->spamcount_WL_WHITEIMPRISON = 0;                 sd->spamtick_WL_WHITEIMPRISON = tick + sd->kdelay;                 break;
			case WL_SOULEXPANSION:                 if (k_tick_check(sd, sd->spamtick_WL_SOULEXPANSION,                 sd->spamcount_WL_SOULEXPANSION,                 battle_config.kd_WL_SOULEXPANSION,                 battle_config.kdw_WL_SOULEXPANSION))                 { sd->spamcount_WL_SOULEXPANSION = sd->k_tick_c; return 0; }                 sd->spamcount_WL_SOULEXPANSION = 0;                 sd->spamtick_WL_SOULEXPANSION = tick + sd->kdelay;                 break;
			case WL_FROSTMISTY:                    if (k_tick_check(sd, sd->spamtick_WL_FROSTMISTY,                    sd->spamcount_WL_FROSTMISTY,                    battle_config.kd_WL_FROSTMISTY,                    battle_config.kdw_WL_FROSTMISTY))                    { sd->spamcount_WL_FROSTMISTY = sd->k_tick_c; return 0; }                    sd->spamcount_WL_FROSTMISTY = 0;                    sd->spamtick_WL_FROSTMISTY = tick + sd->kdelay;                    break;
			case WL_JACKFROST:                     if (k_tick_check(sd, sd->spamtick_WL_JACKFROST,                     sd->spamcount_WL_JACKFROST,                     battle_config.kd_WL_JACKFROST,                     battle_config.kdw_WL_JACKFROST))                     { sd->spamcount_WL_JACKFROST = sd->k_tick_c; return 0; }                     sd->spamcount_WL_JACKFROST = 0;                     sd->spamtick_WL_JACKFROST = tick + sd->kdelay;                     break;
			case WL_MARSHOFABYSS:                  if (k_tick_check(sd, sd->spamtick_WL_MARSHOFABYSS,                  sd->spamcount_WL_MARSHOFABYSS,                  battle_config.kd_WL_MARSHOFABYSS,                  battle_config.kdw_WL_MARSHOFABYSS))                  { sd->spamcount_WL_MARSHOFABYSS = sd->k_tick_c; return 0; }                  sd->spamcount_WL_MARSHOFABYSS = 0;                  sd->spamtick_WL_MARSHOFABYSS = tick + sd->kdelay;                  break;
			case WL_RADIUS:                        if (k_tick_check(sd, sd->spamtick_WL_RADIUS,                        sd->spamcount_WL_RADIUS,                        battle_config.kd_WL_RADIUS,                        battle_config.kdw_WL_RADIUS))                        { sd->spamcount_WL_RADIUS = sd->k_tick_c; return 0; }                        sd->spamcount_WL_RADIUS = 0;                        sd->spamtick_WL_RADIUS = tick + sd->kdelay;                        break;
			case WL_STASIS:                        if (k_tick_check(sd, sd->spamtick_WL_STASIS,                        sd->spamcount_WL_STASIS,                        battle_config.kd_WL_STASIS,                        battle_config.kdw_WL_STASIS))                        { sd->spamcount_WL_STASIS = sd->k_tick_c; return 0; }                        sd->spamcount_WL_STASIS = 0;                        sd->spamtick_WL_STASIS = tick + sd->kdelay;                        break;
			case WL_DRAINLIFE:                     if (k_tick_check(sd, sd->spamtick_WL_DRAINLIFE,                     sd->spamcount_WL_DRAINLIFE,                     battle_config.kd_WL_DRAINLIFE,                     battle_config.kdw_WL_DRAINLIFE))                     { sd->spamcount_WL_DRAINLIFE = sd->k_tick_c; return 0; }                     sd->spamcount_WL_DRAINLIFE = 0;                     sd->spamtick_WL_DRAINLIFE = tick + sd->kdelay;                     break;
			case WL_CRIMSONROCK:                   if (k_tick_check(sd, sd->spamtick_WL_CRIMSONROCK,                   sd->spamcount_WL_CRIMSONROCK,                   battle_config.kd_WL_CRIMSONROCK,                   battle_config.kdw_WL_CRIMSONROCK))                   { sd->spamcount_WL_CRIMSONROCK = sd->k_tick_c; return 0; }                   sd->spamcount_WL_CRIMSONROCK = 0;                   sd->spamtick_WL_CRIMSONROCK = tick + sd->kdelay;                   break;
			case WL_HELLINFERNO:                   if (k_tick_check(sd, sd->spamtick_WL_HELLINFERNO,                   sd->spamcount_WL_HELLINFERNO,                   battle_config.kd_WL_HELLINFERNO,                   battle_config.kdw_WL_HELLINFERNO))                   { sd->spamcount_WL_HELLINFERNO = sd->k_tick_c; return 0; }                   sd->spamcount_WL_HELLINFERNO = 0;                   sd->spamtick_WL_HELLINFERNO = tick + sd->kdelay;                   break;
			case WL_COMET:                         if (k_tick_check(sd, sd->spamtick_WL_COMET,                         sd->spamcount_WL_COMET,                         battle_config.kd_WL_COMET,                         battle_config.kdw_WL_COMET))                         { sd->spamcount_WL_COMET = sd->k_tick_c; return 0; }                         sd->spamcount_WL_COMET = 0;                         sd->spamtick_WL_COMET = tick + sd->kdelay;                         break;
			case WL_CHAINLIGHTNING:                if (k_tick_check(sd, sd->spamtick_WL_CHAINLIGHTNING,                sd->spamcount_WL_CHAINLIGHTNING,                battle_config.kd_WL_CHAINLIGHTNING,                battle_config.kdw_WL_CHAINLIGHTNING))                { sd->spamcount_WL_CHAINLIGHTNING = sd->k_tick_c; return 0; }                sd->spamcount_WL_CHAINLIGHTNING = 0;                sd->spamtick_WL_CHAINLIGHTNING = tick + sd->kdelay;                break;
			case WL_EARTHSTRAIN:                   if (k_tick_check(sd, sd->spamtick_WL_EARTHSTRAIN,                   sd->spamcount_WL_EARTHSTRAIN,                   battle_config.kd_WL_EARTHSTRAIN,                   battle_config.kdw_WL_EARTHSTRAIN))                   { sd->spamcount_WL_EARTHSTRAIN = sd->k_tick_c; return 0; }                   sd->spamcount_WL_EARTHSTRAIN = 0;                   sd->spamtick_WL_EARTHSTRAIN = tick + sd->kdelay;                   break;
			case WL_TETRAVORTEX:                   if (k_tick_check(sd, sd->spamtick_WL_TETRAVORTEX,                   sd->spamcount_WL_TETRAVORTEX,                   battle_config.kd_WL_TETRAVORTEX,                   battle_config.kdw_WL_TETRAVORTEX))                   { sd->spamcount_WL_TETRAVORTEX = sd->k_tick_c; return 0; }                   sd->spamcount_WL_TETRAVORTEX = 0;                   sd->spamtick_WL_TETRAVORTEX = tick + sd->kdelay;                   break;
			case WL_RELEASE:                       if (k_tick_check(sd, sd->spamtick_WL_RELEASE,                       sd->spamcount_WL_RELEASE,                       battle_config.kd_WL_RELEASE,                       battle_config.kdw_WL_RELEASE))                       { sd->spamcount_WL_RELEASE = sd->k_tick_c; return 0; }                       sd->spamcount_WL_RELEASE = 0;                       sd->spamtick_WL_RELEASE = tick + sd->kdelay;                       break;
			case WL_READING_SB:                    if (k_tick_check(sd, sd->spamtick_WL_READING_SB,                    sd->spamcount_WL_READING_SB,                    battle_config.kd_WL_READING_SB,                    battle_config.kdw_WL_READING_SB))                    { sd->spamcount_WL_READING_SB = sd->k_tick_c; return 0; }                    sd->spamcount_WL_READING_SB = 0;                    sd->spamtick_WL_READING_SB = tick + sd->kdelay;                    break;
			case WL_FREEZE_SP:                     if (k_tick_check(sd, sd->spamtick_WL_FREEZE_SP,                     sd->spamcount_WL_FREEZE_SP,                     battle_config.kd_WL_FREEZE_SP,                     battle_config.kdw_WL_FREEZE_SP))                     { sd->spamcount_WL_FREEZE_SP = sd->k_tick_c; return 0; }                     sd->spamcount_WL_FREEZE_SP = 0;                     sd->spamtick_WL_FREEZE_SP = tick + sd->kdelay;                     break;
			case RA_ARROWSTORM:                    if (k_tick_check(sd, sd->spamtick_RA_ARROWSTORM,                    sd->spamcount_RA_ARROWSTORM,                    battle_config.kd_RA_ARROWSTORM,                    battle_config.kdw_RA_ARROWSTORM))                    { sd->spamcount_RA_ARROWSTORM = sd->k_tick_c; return 0; }                    sd->spamcount_RA_ARROWSTORM = 0;                    sd->spamtick_RA_ARROWSTORM = tick + sd->kdelay;                    break;
			case RA_AIMEDBOLT:                     if (k_tick_check(sd, sd->spamtick_RA_AIMEDBOLT,                     sd->spamcount_RA_AIMEDBOLT,                     battle_config.kd_RA_AIMEDBOLT,                     battle_config.kdw_RA_AIMEDBOLT))                     { sd->spamcount_RA_AIMEDBOLT = sd->k_tick_c; return 0; }                     sd->spamcount_RA_AIMEDBOLT = 0;                     sd->spamtick_RA_AIMEDBOLT = tick + sd->kdelay;                     break;
			case RA_WUGSTRIKE:                     if (k_tick_check(sd, sd->spamtick_RA_WUGSTRIKE,                     sd->spamcount_RA_WUGSTRIKE,                     battle_config.kd_RA_WUGSTRIKE,                     battle_config.kdw_RA_WUGSTRIKE))                     { sd->spamcount_RA_WUGSTRIKE = sd->k_tick_c; return 0; }                     sd->spamcount_RA_WUGSTRIKE = 0;                     sd->spamtick_RA_WUGSTRIKE = tick + sd->kdelay;                     break;
			case RA_WUGBITE:                       if (k_tick_check(sd, sd->spamtick_RA_WUGBITE,                       sd->spamcount_RA_WUGBITE,                       battle_config.kd_RA_WUGBITE,                       battle_config.kdw_RA_WUGBITE))                       { sd->spamcount_RA_WUGBITE = sd->k_tick_c; return 0; }                       sd->spamcount_RA_WUGBITE = 0;                       sd->spamtick_RA_WUGBITE = tick + sd->kdelay;                       break;
			case NC_BOOSTKNUCKLE:                  if (k_tick_check(sd, sd->spamtick_NC_BOOSTKNUCKLE,                  sd->spamcount_NC_BOOSTKNUCKLE,                  battle_config.kd_NC_BOOSTKNUCKLE,                  battle_config.kdw_NC_BOOSTKNUCKLE))                  { sd->spamcount_NC_BOOSTKNUCKLE = sd->k_tick_c; return 0; }                  sd->spamcount_NC_BOOSTKNUCKLE = 0;                  sd->spamtick_NC_BOOSTKNUCKLE = tick + sd->kdelay;                  break;
			case NC_PILEBUNKER:                    if (k_tick_check(sd, sd->spamtick_NC_PILEBUNKER,                    sd->spamcount_NC_PILEBUNKER,                    battle_config.kd_NC_PILEBUNKER,                    battle_config.kdw_NC_PILEBUNKER))                    { sd->spamcount_NC_PILEBUNKER = sd->k_tick_c; return 0; }                    sd->spamcount_NC_PILEBUNKER = 0;                    sd->spamtick_NC_PILEBUNKER = tick + sd->kdelay;                    break;
			case NC_VULCANARM:                     if (k_tick_check(sd, sd->spamtick_NC_VULCANARM,                     sd->spamcount_NC_VULCANARM,                     battle_config.kd_NC_VULCANARM,                     battle_config.kdw_NC_VULCANARM))                     { sd->spamcount_NC_VULCANARM = sd->k_tick_c; return 0; }                     sd->spamcount_NC_VULCANARM = 0;                     sd->spamtick_NC_VULCANARM = tick + sd->kdelay;                     break;
			case NC_FLAMELAUNCHER:                 if (k_tick_check(sd, sd->spamtick_NC_FLAMELAUNCHER,                 sd->spamcount_NC_FLAMELAUNCHER,                 battle_config.kd_NC_FLAMELAUNCHER,                 battle_config.kdw_NC_FLAMELAUNCHER))                 { sd->spamcount_NC_FLAMELAUNCHER = sd->k_tick_c; return 0; }                 sd->spamcount_NC_FLAMELAUNCHER = 0;                 sd->spamtick_NC_FLAMELAUNCHER = tick + sd->kdelay;                 break;
			case NC_COLDSLOWER:                    if (k_tick_check(sd, sd->spamtick_NC_COLDSLOWER,                    sd->spamcount_NC_COLDSLOWER,                    battle_config.kd_NC_COLDSLOWER,                    battle_config.kdw_NC_COLDSLOWER))                    { sd->spamcount_NC_COLDSLOWER = sd->k_tick_c; return 0; }                    sd->spamcount_NC_COLDSLOWER = 0;                    sd->spamtick_NC_COLDSLOWER = tick + sd->kdelay;                    break;
			case NC_ARMSCANNON:                    if (k_tick_check(sd, sd->spamtick_NC_ARMSCANNON,                    sd->spamcount_NC_ARMSCANNON,                    battle_config.kd_NC_ARMSCANNON,                    battle_config.kdw_NC_ARMSCANNON))                    { sd->spamcount_NC_ARMSCANNON = sd->k_tick_c; return 0; }                    sd->spamcount_NC_ARMSCANNON = 0;                    sd->spamtick_NC_ARMSCANNON = tick + sd->kdelay;                    break;
			case NC_ACCELERATION:                  if (k_tick_check(sd, sd->spamtick_NC_ACCELERATION,                  sd->spamcount_NC_ACCELERATION,                  battle_config.kd_NC_ACCELERATION,                  battle_config.kdw_NC_ACCELERATION))                  { sd->spamcount_NC_ACCELERATION = sd->k_tick_c; return 0; }                  sd->spamcount_NC_ACCELERATION = 0;                  sd->spamtick_NC_ACCELERATION = tick + sd->kdelay;                  break;
			case NC_F_SIDESLIDE:                   if (k_tick_check(sd, sd->spamtick_NC_F_SIDESLIDE,                   sd->spamcount_NC_F_SIDESLIDE,                   battle_config.kd_NC_F_SIDESLIDE,                   battle_config.kdw_NC_F_SIDESLIDE))                   { sd->spamcount_NC_F_SIDESLIDE = sd->k_tick_c; return 0; }                   sd->spamcount_NC_F_SIDESLIDE = 0;                   sd->spamtick_NC_F_SIDESLIDE = tick + sd->kdelay;                   break;
			case NC_B_SIDESLIDE:                   if (k_tick_check(sd, sd->spamtick_NC_B_SIDESLIDE,                   sd->spamcount_NC_B_SIDESLIDE,                   battle_config.kd_NC_B_SIDESLIDE,                   battle_config.kdw_NC_B_SIDESLIDE))                   { sd->spamcount_NC_B_SIDESLIDE = sd->k_tick_c; return 0; }                   sd->spamcount_NC_B_SIDESLIDE = 0;                   sd->spamtick_NC_B_SIDESLIDE = tick + sd->kdelay;                   break;
			case NC_MAINFRAME:                     if (k_tick_check(sd, sd->spamtick_NC_MAINFRAME,                     sd->spamcount_NC_MAINFRAME,                     battle_config.kd_NC_MAINFRAME,                     battle_config.kdw_NC_MAINFRAME))                     { sd->spamcount_NC_MAINFRAME = sd->k_tick_c; return 0; }                     sd->spamcount_NC_MAINFRAME = 0;                     sd->spamtick_NC_MAINFRAME = tick + sd->kdelay;                     break;
			case NC_SHAPESHIFT:                    if (k_tick_check(sd, sd->spamtick_NC_SHAPESHIFT,                    sd->spamcount_NC_SHAPESHIFT,                    battle_config.kd_NC_SHAPESHIFT,                    battle_config.kdw_NC_SHAPESHIFT))                    { sd->spamcount_NC_SHAPESHIFT = sd->k_tick_c; return 0; }                    sd->spamcount_NC_SHAPESHIFT = 0;                    sd->spamtick_NC_SHAPESHIFT = tick + sd->kdelay;                    break;
			case NC_INFRAREDSCAN:                  if (k_tick_check(sd, sd->spamtick_NC_INFRAREDSCAN,                  sd->spamcount_NC_INFRAREDSCAN,                  battle_config.kd_NC_INFRAREDSCAN,                  battle_config.kdw_NC_INFRAREDSCAN))                  { sd->spamcount_NC_INFRAREDSCAN = sd->k_tick_c; return 0; }                  sd->spamcount_NC_INFRAREDSCAN = 0;                  sd->spamtick_NC_INFRAREDSCAN = tick + sd->kdelay;                  break;
			case NC_ANALYZE:                       if (k_tick_check(sd, sd->spamtick_NC_ANALYZE,                       sd->spamcount_NC_ANALYZE,                       battle_config.kd_NC_ANALYZE,                       battle_config.kdw_NC_ANALYZE))                       { sd->spamcount_NC_ANALYZE = sd->k_tick_c; return 0; }                       sd->spamcount_NC_ANALYZE = 0;                       sd->spamtick_NC_ANALYZE = tick + sd->kdelay;                       break;
			case NC_MAGNETICFIELD:                 if (k_tick_check(sd, sd->spamtick_NC_MAGNETICFIELD,                 sd->spamcount_NC_MAGNETICFIELD,                 battle_config.kd_NC_MAGNETICFIELD,                 battle_config.kdw_NC_MAGNETICFIELD))                 { sd->spamcount_NC_MAGNETICFIELD = sd->k_tick_c; return 0; }                 sd->spamcount_NC_MAGNETICFIELD = 0;                 sd->spamtick_NC_MAGNETICFIELD = tick + sd->kdelay;                 break;
			case NC_NEUTRALBARRIER:                if (k_tick_check(sd, sd->spamtick_NC_NEUTRALBARRIER,                sd->spamcount_NC_NEUTRALBARRIER,                battle_config.kd_NC_NEUTRALBARRIER,                battle_config.kdw_NC_NEUTRALBARRIER))                { sd->spamcount_NC_NEUTRALBARRIER = sd->k_tick_c; return 0; }                sd->spamcount_NC_NEUTRALBARRIER = 0;                sd->spamtick_NC_NEUTRALBARRIER = tick + sd->kdelay;                break;
			case NC_STEALTHFIELD:                  if (k_tick_check(sd, sd->spamtick_NC_STEALTHFIELD,                  sd->spamcount_NC_STEALTHFIELD,                  battle_config.kd_NC_STEALTHFIELD,                  battle_config.kdw_NC_STEALTHFIELD))                  { sd->spamcount_NC_STEALTHFIELD = sd->k_tick_c; return 0; }                  sd->spamcount_NC_STEALTHFIELD = 0;                  sd->spamtick_NC_STEALTHFIELD = tick + sd->kdelay;                  break;
			case NC_AXEBOOMERANG:                  if (k_tick_check(sd, sd->spamtick_NC_AXEBOOMERANG,                  sd->spamcount_NC_AXEBOOMERANG,                  battle_config.kd_NC_AXEBOOMERANG,                  battle_config.kdw_NC_AXEBOOMERANG))                  { sd->spamcount_NC_AXEBOOMERANG = sd->k_tick_c; return 0; }                  sd->spamcount_NC_AXEBOOMERANG = 0;                  sd->spamtick_NC_AXEBOOMERANG = tick + sd->kdelay;                  break;
			case NC_POWERSWING:                    if (k_tick_check(sd, sd->spamtick_NC_POWERSWING,                    sd->spamcount_NC_POWERSWING,                    battle_config.kd_NC_POWERSWING,                    battle_config.kdw_NC_POWERSWING))                    { sd->spamcount_NC_POWERSWING = sd->k_tick_c; return 0; }                    sd->spamcount_NC_POWERSWING = 0;                    sd->spamtick_NC_POWERSWING = tick + sd->kdelay;                    break;
			case NC_AXETORNADO:                    if (k_tick_check(sd, sd->spamtick_NC_AXETORNADO,                    sd->spamcount_NC_AXETORNADO,                    battle_config.kd_NC_AXETORNADO,                    battle_config.kdw_NC_AXETORNADO))                    { sd->spamcount_NC_AXETORNADO = sd->k_tick_c; return 0; }                    sd->spamcount_NC_AXETORNADO = 0;                    sd->spamtick_NC_AXETORNADO = tick + sd->kdelay;                    break;
			case NC_SILVERSNIPER:                  if (k_tick_check(sd, sd->spamtick_NC_SILVERSNIPER,                  sd->spamcount_NC_SILVERSNIPER,                  battle_config.kd_NC_SILVERSNIPER,                  battle_config.kdw_NC_SILVERSNIPER))                  { sd->spamcount_NC_SILVERSNIPER = sd->k_tick_c; return 0; }                  sd->spamcount_NC_SILVERSNIPER = 0;                  sd->spamtick_NC_SILVERSNIPER = tick + sd->kdelay;                  break;
			case NC_MAGICDECOY:                    if (k_tick_check(sd, sd->spamtick_NC_MAGICDECOY,                    sd->spamcount_NC_MAGICDECOY,                    battle_config.kd_NC_MAGICDECOY,                    battle_config.kdw_NC_MAGICDECOY))                    { sd->spamcount_NC_MAGICDECOY = sd->k_tick_c; return 0; }                    sd->spamcount_NC_MAGICDECOY = 0;                    sd->spamtick_NC_MAGICDECOY = tick + sd->kdelay;                    break;
			case NC_DISJOINT:                      if (k_tick_check(sd, sd->spamtick_NC_DISJOINT,                      sd->spamcount_NC_DISJOINT,                      battle_config.kd_NC_DISJOINT,                      battle_config.kdw_NC_DISJOINT))                      { sd->spamcount_NC_DISJOINT = sd->k_tick_c; return 0; }                      sd->spamcount_NC_DISJOINT = 0;                      sd->spamtick_NC_DISJOINT = tick + sd->kdelay;                      break;
			case SC_FATALMENACE:                   if (k_tick_check(sd, sd->spamtick_SC_FATALMENACE,                   sd->spamcount_SC_FATALMENACE,                   battle_config.kd_SC_FATALMENACE,                   battle_config.kdw_SC_FATALMENACE))                   { sd->spamcount_SC_FATALMENACE = sd->k_tick_c; return 0; }                   sd->spamcount_SC_FATALMENACE = 0;                   sd->spamtick_SC_FATALMENACE = tick + sd->kdelay;                   break;
			case SC_TRIANGLESHOT:                  if (k_tick_check(sd, sd->spamtick_SC_TRIANGLESHOT,                  sd->spamcount_SC_TRIANGLESHOT,                  battle_config.kd_SC_TRIANGLESHOT,                  battle_config.kdw_SC_TRIANGLESHOT))                  { sd->spamcount_SC_TRIANGLESHOT = sd->k_tick_c; return 0; }                  sd->spamcount_SC_TRIANGLESHOT = 0;                  sd->spamtick_SC_TRIANGLESHOT = tick + sd->kdelay;                  break;
			case SC_INVISIBILITY:                  if (k_tick_check(sd, sd->spamtick_SC_INVISIBILITY,                  sd->spamcount_SC_INVISIBILITY,                  battle_config.kd_SC_INVISIBILITY,                  battle_config.kdw_SC_INVISIBILITY))                  { sd->spamcount_SC_INVISIBILITY = sd->k_tick_c; return 0; }                  sd->spamcount_SC_INVISIBILITY = 0;                  sd->spamtick_SC_INVISIBILITY = tick + sd->kdelay;                  break;
			case SC_ENERVATION:                    if (k_tick_check(sd, sd->spamtick_SC_ENERVATION,                    sd->spamcount_SC_ENERVATION,                    battle_config.kd_SC_ENERVATION,                    battle_config.kdw_SC_ENERVATION))                    { sd->spamcount_SC_ENERVATION = sd->k_tick_c; return 0; }                    sd->spamcount_SC_ENERVATION = 0;                    sd->spamtick_SC_ENERVATION = tick + sd->kdelay;                    break;
			case SC_GROOMY:                        if (k_tick_check(sd, sd->spamtick_SC_GROOMY,                        sd->spamcount_SC_GROOMY,                        battle_config.kd_SC_GROOMY,                        battle_config.kdw_SC_GROOMY))                        { sd->spamcount_SC_GROOMY = sd->k_tick_c; return 0; }                        sd->spamcount_SC_GROOMY = 0;                        sd->spamtick_SC_GROOMY = tick + sd->kdelay;                        break;
			case SC_IGNORANCE:                     if (k_tick_check(sd, sd->spamtick_SC_IGNORANCE,                     sd->spamcount_SC_IGNORANCE,                     battle_config.kd_SC_IGNORANCE,                     battle_config.kdw_SC_IGNORANCE))                     { sd->spamcount_SC_IGNORANCE = sd->k_tick_c; return 0; }                     sd->spamcount_SC_IGNORANCE = 0;                     sd->spamtick_SC_IGNORANCE = tick + sd->kdelay;                     break;
			case SC_LAZINESS:                      if (k_tick_check(sd, sd->spamtick_SC_LAZINESS,                      sd->spamcount_SC_LAZINESS,                      battle_config.kd_SC_LAZINESS,                      battle_config.kdw_SC_LAZINESS))                      { sd->spamcount_SC_LAZINESS = sd->k_tick_c; return 0; }                      sd->spamcount_SC_LAZINESS = 0;                      sd->spamtick_SC_LAZINESS = tick + sd->kdelay;                      break;
			case SC_UNLUCKY:                       if (k_tick_check(sd, sd->spamtick_SC_UNLUCKY,                       sd->spamcount_SC_UNLUCKY,                       battle_config.kd_SC_UNLUCKY,                       battle_config.kdw_SC_UNLUCKY))                       { sd->spamcount_SC_UNLUCKY = sd->k_tick_c; return 0; }                       sd->spamcount_SC_UNLUCKY = 0;                       sd->spamtick_SC_UNLUCKY = tick + sd->kdelay;                       break;
			case SC_WEAKNESS:                      if (k_tick_check(sd, sd->spamtick_SC_WEAKNESS,                      sd->spamcount_SC_WEAKNESS,                      battle_config.kd_SC_WEAKNESS,                      battle_config.kdw_SC_WEAKNESS))                      { sd->spamcount_SC_WEAKNESS = sd->k_tick_c; return 0; }                      sd->spamcount_SC_WEAKNESS = 0;                      sd->spamtick_SC_WEAKNESS = tick + sd->kdelay;                      break;
			case SC_STRIPACCESSARY:                if (k_tick_check(sd, sd->spamtick_SC_STRIPACCESSARY,                sd->spamcount_SC_STRIPACCESSARY,                battle_config.kd_SC_STRIPACCESSARY,                battle_config.kdw_SC_STRIPACCESSARY))                { sd->spamcount_SC_STRIPACCESSARY = sd->k_tick_c; return 0; }                sd->spamcount_SC_STRIPACCESSARY = 0;                sd->spamtick_SC_STRIPACCESSARY = tick + sd->kdelay;                break;
			case SC_MANHOLE:                       if (k_tick_check(sd, sd->spamtick_SC_MANHOLE,                       sd->spamcount_SC_MANHOLE,                       battle_config.kd_SC_MANHOLE,                       battle_config.kdw_SC_MANHOLE))                       { sd->spamcount_SC_MANHOLE = sd->k_tick_c; return 0; }                       sd->spamcount_SC_MANHOLE = 0;                       sd->spamtick_SC_MANHOLE = tick + sd->kdelay;                       break;
			case SC_DIMENSIONDOOR:                 if (k_tick_check(sd, sd->spamtick_SC_DIMENSIONDOOR,                 sd->spamcount_SC_DIMENSIONDOOR,                 battle_config.kd_SC_DIMENSIONDOOR,                 battle_config.kdw_SC_DIMENSIONDOOR))                 { sd->spamcount_SC_DIMENSIONDOOR = sd->k_tick_c; return 0; }                 sd->spamcount_SC_DIMENSIONDOOR = 0;                 sd->spamtick_SC_DIMENSIONDOOR = tick + sd->kdelay;                 break;
			case SC_CHAOSPANIC:                    if (k_tick_check(sd, sd->spamtick_SC_CHAOSPANIC,                    sd->spamcount_SC_CHAOSPANIC,                    battle_config.kd_SC_CHAOSPANIC,                    battle_config.kdw_SC_CHAOSPANIC))                    { sd->spamcount_SC_CHAOSPANIC = sd->k_tick_c; return 0; }                    sd->spamcount_SC_CHAOSPANIC = 0;                    sd->spamtick_SC_CHAOSPANIC = tick + sd->kdelay;                    break;
			case SC_MAELSTROM:                     if (k_tick_check(sd, sd->spamtick_SC_MAELSTROM,                     sd->spamcount_SC_MAELSTROM,                     battle_config.kd_SC_MAELSTROM,                     battle_config.kdw_SC_MAELSTROM))                     { sd->spamcount_SC_MAELSTROM = sd->k_tick_c; return 0; }                     sd->spamcount_SC_MAELSTROM = 0;                     sd->spamtick_SC_MAELSTROM = tick + sd->kdelay;                     break;
			case SC_BLOODYLUST:                    if (k_tick_check(sd, sd->spamtick_SC_BLOODYLUST,                    sd->spamcount_SC_BLOODYLUST,                    battle_config.kd_SC_BLOODYLUST,                    battle_config.kdw_SC_BLOODYLUST))                    { sd->spamcount_SC_BLOODYLUST = sd->k_tick_c; return 0; }                    sd->spamcount_SC_BLOODYLUST = 0;                    sd->spamtick_SC_BLOODYLUST = tick + sd->kdelay;                    break;
			case SC_FEINTBOMB:                     if (k_tick_check(sd, sd->spamtick_SC_FEINTBOMB,                     sd->spamcount_SC_FEINTBOMB,                     battle_config.kd_SC_FEINTBOMB,                     battle_config.kdw_SC_FEINTBOMB))                     { sd->spamcount_SC_FEINTBOMB = sd->k_tick_c; return 0; }                     sd->spamcount_SC_FEINTBOMB = 0;                     sd->spamtick_SC_FEINTBOMB = tick + sd->kdelay;                     break;
			case LG_CANNONSPEAR:                   if (k_tick_check(sd, sd->spamtick_LG_CANNONSPEAR,                   sd->spamcount_LG_CANNONSPEAR,                   battle_config.kd_LG_CANNONSPEAR,                   battle_config.kdw_LG_CANNONSPEAR))                   { sd->spamcount_LG_CANNONSPEAR = sd->k_tick_c; return 0; }                   sd->spamcount_LG_CANNONSPEAR = 0;                   sd->spamtick_LG_CANNONSPEAR = tick + sd->kdelay;                   break;
			case LG_BANISHINGPOINT:                if (k_tick_check(sd, sd->spamtick_LG_BANISHINGPOINT,                sd->spamcount_LG_BANISHINGPOINT,                battle_config.kd_LG_BANISHINGPOINT,                battle_config.kdw_LG_BANISHINGPOINT))                { sd->spamcount_LG_BANISHINGPOINT = sd->k_tick_c; return 0; }                sd->spamcount_LG_BANISHINGPOINT = 0;                sd->spamtick_LG_BANISHINGPOINT = tick + sd->kdelay;                break;
			case LG_TRAMPLE:                       if (k_tick_check(sd, sd->spamtick_LG_TRAMPLE,                       sd->spamcount_LG_TRAMPLE,                       battle_config.kd_LG_TRAMPLE,                       battle_config.kdw_LG_TRAMPLE))                       { sd->spamcount_LG_TRAMPLE = sd->k_tick_c; return 0; }                       sd->spamcount_LG_TRAMPLE = 0;                       sd->spamtick_LG_TRAMPLE = tick + sd->kdelay;                       break;
			case LG_PINPOINTATTACK:                if (k_tick_check(sd, sd->spamtick_LG_PINPOINTATTACK,                sd->spamcount_LG_PINPOINTATTACK,                battle_config.kd_LG_PINPOINTATTACK,                battle_config.kdw_LG_PINPOINTATTACK))                { sd->spamcount_LG_PINPOINTATTACK = sd->k_tick_c; return 0; }                sd->spamcount_LG_PINPOINTATTACK = 0;                sd->spamtick_LG_PINPOINTATTACK = tick + sd->kdelay;                break;
			case LG_RAGEBURST:                     if (k_tick_check(sd, sd->spamtick_LG_RAGEBURST,                     sd->spamcount_LG_RAGEBURST,                     battle_config.kd_LG_RAGEBURST,                     battle_config.kdw_LG_RAGEBURST))                     { sd->spamcount_LG_RAGEBURST = sd->k_tick_c; return 0; }                     sd->spamcount_LG_RAGEBURST = 0;                     sd->spamtick_LG_RAGEBURST = tick + sd->kdelay;                     break;
			case LG_EXEEDBREAK:                    if (k_tick_check(sd, sd->spamtick_LG_EXEEDBREAK,                    sd->spamcount_LG_EXEEDBREAK,                    battle_config.kd_LG_EXEEDBREAK,                    battle_config.kdw_LG_EXEEDBREAK))                    { sd->spamcount_LG_EXEEDBREAK = sd->k_tick_c; return 0; }                    sd->spamcount_LG_EXEEDBREAK = 0;                    sd->spamtick_LG_EXEEDBREAK = tick + sd->kdelay;                    break;
			case LG_OVERBRAND:                     if (k_tick_check(sd, sd->spamtick_LG_OVERBRAND,                     sd->spamcount_LG_OVERBRAND,                     battle_config.kd_LG_OVERBRAND,                     battle_config.kdw_LG_OVERBRAND))                     { sd->spamcount_LG_OVERBRAND = sd->k_tick_c; return 0; }                     sd->spamcount_LG_OVERBRAND = 0;                     sd->spamtick_LG_OVERBRAND = tick + sd->kdelay;                     break;
			case LG_BANDING:                       if (k_tick_check(sd, sd->spamtick_LG_BANDING,                       sd->spamcount_LG_BANDING,                       battle_config.kd_LG_BANDING,                       battle_config.kdw_LG_BANDING))                       { sd->spamcount_LG_BANDING = sd->k_tick_c; return 0; }                       sd->spamcount_LG_BANDING = 0;                       sd->spamtick_LG_BANDING = tick + sd->kdelay;                       break;
			case LG_MOONSLASHER:                   if (k_tick_check(sd, sd->spamtick_LG_MOONSLASHER,                   sd->spamcount_LG_MOONSLASHER,                   battle_config.kd_LG_MOONSLASHER,                   battle_config.kdw_LG_MOONSLASHER))                   { sd->spamcount_LG_MOONSLASHER = sd->k_tick_c; return 0; }                   sd->spamcount_LG_MOONSLASHER = 0;                   sd->spamtick_LG_MOONSLASHER = tick + sd->kdelay;                   break;
			case LG_RAYOFGENESIS:                  if (k_tick_check(sd, sd->spamtick_LG_RAYOFGENESIS,                  sd->spamcount_LG_RAYOFGENESIS,                  battle_config.kd_LG_RAYOFGENESIS,                  battle_config.kdw_LG_RAYOFGENESIS))                  { sd->spamcount_LG_RAYOFGENESIS = sd->k_tick_c; return 0; }                  sd->spamcount_LG_RAYOFGENESIS = 0;                  sd->spamtick_LG_RAYOFGENESIS = tick + sd->kdelay;                  break;
			case LG_PIETY:                         if (k_tick_check(sd, sd->spamtick_LG_PIETY,                         sd->spamcount_LG_PIETY,                         battle_config.kd_LG_PIETY,                         battle_config.kdw_LG_PIETY))                         { sd->spamcount_LG_PIETY = sd->k_tick_c; return 0; }                         sd->spamcount_LG_PIETY = 0;                         sd->spamtick_LG_PIETY = tick + sd->kdelay;                         break;
			case LG_EARTHDRIVE:                    if (k_tick_check(sd, sd->spamtick_LG_EARTHDRIVE,                    sd->spamcount_LG_EARTHDRIVE,                    battle_config.kd_LG_EARTHDRIVE,                    battle_config.kdw_LG_EARTHDRIVE))                    { sd->spamcount_LG_EARTHDRIVE = sd->k_tick_c; return 0; }                    sd->spamcount_LG_EARTHDRIVE = 0;                    sd->spamtick_LG_EARTHDRIVE = tick + sd->kdelay;                    break;
			case LG_HESPERUSLIT:                   if (k_tick_check(sd, sd->spamtick_LG_HESPERUSLIT,                   sd->spamcount_LG_HESPERUSLIT,                   battle_config.kd_LG_HESPERUSLIT,                   battle_config.kdw_LG_HESPERUSLIT))                   { sd->spamcount_LG_HESPERUSLIT = sd->k_tick_c; return 0; }                   sd->spamcount_LG_HESPERUSLIT = 0;                   sd->spamtick_LG_HESPERUSLIT = tick + sd->kdelay;                   break;
			case SR_DRAGONCOMBO:                   if (k_tick_check(sd, sd->spamtick_SR_DRAGONCOMBO,                   sd->spamcount_SR_DRAGONCOMBO,                   battle_config.kd_SR_DRAGONCOMBO,                   battle_config.kdw_SR_DRAGONCOMBO))                   { sd->spamcount_SR_DRAGONCOMBO = sd->k_tick_c; return 0; }                   sd->spamcount_SR_DRAGONCOMBO = 0;                   sd->spamtick_SR_DRAGONCOMBO = tick + sd->kdelay;                   break;
			case SR_SKYNETBLOW:                    if (k_tick_check(sd, sd->spamtick_SR_SKYNETBLOW,                    sd->spamcount_SR_SKYNETBLOW,                    battle_config.kd_SR_SKYNETBLOW,                    battle_config.kdw_SR_SKYNETBLOW))                    { sd->spamcount_SR_SKYNETBLOW = sd->k_tick_c; return 0; }                    sd->spamcount_SR_SKYNETBLOW = 0;                    sd->spamtick_SR_SKYNETBLOW = tick + sd->kdelay;                    break;
			case SR_EARTHSHAKER:                   if (k_tick_check(sd, sd->spamtick_SR_EARTHSHAKER,                   sd->spamcount_SR_EARTHSHAKER,                   battle_config.kd_SR_EARTHSHAKER,                   battle_config.kdw_SR_EARTHSHAKER))                   { sd->spamcount_SR_EARTHSHAKER = sd->k_tick_c; return 0; }                   sd->spamcount_SR_EARTHSHAKER = 0;                   sd->spamtick_SR_EARTHSHAKER = tick + sd->kdelay;                   break;
			case SR_FALLENEMPIRE:                  if (k_tick_check(sd, sd->spamtick_SR_FALLENEMPIRE,                  sd->spamcount_SR_FALLENEMPIRE,                  battle_config.kd_SR_FALLENEMPIRE,                  battle_config.kdw_SR_FALLENEMPIRE))                  { sd->spamcount_SR_FALLENEMPIRE = sd->k_tick_c; return 0; }                  sd->spamcount_SR_FALLENEMPIRE = 0;                  sd->spamtick_SR_FALLENEMPIRE = tick + sd->kdelay;                  break;
			case SR_TIGERCANNON:                   if (k_tick_check(sd, sd->spamtick_SR_TIGERCANNON,                   sd->spamcount_SR_TIGERCANNON,                   battle_config.kd_SR_TIGERCANNON,                   battle_config.kdw_SR_TIGERCANNON))                   { sd->spamcount_SR_TIGERCANNON = sd->k_tick_c; return 0; }                   sd->spamcount_SR_TIGERCANNON = 0;                   sd->spamtick_SR_TIGERCANNON = tick + sd->kdelay;                   break;
			case SR_HELLGATE:                      if (k_tick_check(sd, sd->spamtick_SR_HELLGATE,                      sd->spamcount_SR_HELLGATE,                      battle_config.kd_SR_HELLGATE,                      battle_config.kdw_SR_HELLGATE))                      { sd->spamcount_SR_HELLGATE = sd->k_tick_c; return 0; }                      sd->spamcount_SR_HELLGATE = 0;                      sd->spamtick_SR_HELLGATE = tick + sd->kdelay;                      break;
			case SR_RAMPAGEBLASTER:                if (k_tick_check(sd, sd->spamtick_SR_RAMPAGEBLASTER,                sd->spamcount_SR_RAMPAGEBLASTER,                battle_config.kd_SR_RAMPAGEBLASTER,                battle_config.kdw_SR_RAMPAGEBLASTER))                { sd->spamcount_SR_RAMPAGEBLASTER = sd->k_tick_c; return 0; }                sd->spamcount_SR_RAMPAGEBLASTER = 0;                sd->spamtick_SR_RAMPAGEBLASTER = tick + sd->kdelay;                break;
			case SR_CRESCENTELBOW:                 if (k_tick_check(sd, sd->spamtick_SR_CRESCENTELBOW,                 sd->spamcount_SR_CRESCENTELBOW,                 battle_config.kd_SR_CRESCENTELBOW,                 battle_config.kdw_SR_CRESCENTELBOW))                 { sd->spamcount_SR_CRESCENTELBOW = sd->k_tick_c; return 0; }                 sd->spamcount_SR_CRESCENTELBOW = 0;                 sd->spamtick_SR_CRESCENTELBOW = tick + sd->kdelay;                 break;
			case SR_CURSEDCIRCLE:                  if (k_tick_check(sd, sd->spamtick_SR_CURSEDCIRCLE,                  sd->spamcount_SR_CURSEDCIRCLE,                  battle_config.kd_SR_CURSEDCIRCLE,                  battle_config.kdw_SR_CURSEDCIRCLE))                  { sd->spamcount_SR_CURSEDCIRCLE = sd->k_tick_c; return 0; }                  sd->spamcount_SR_CURSEDCIRCLE = 0;                  sd->spamtick_SR_CURSEDCIRCLE = tick + sd->kdelay;                  break;
			case SR_LIGHTNINGWALK:                 if (k_tick_check(sd, sd->spamtick_SR_LIGHTNINGWALK,                 sd->spamcount_SR_LIGHTNINGWALK,                 battle_config.kd_SR_LIGHTNINGWALK,                 battle_config.kdw_SR_LIGHTNINGWALK))                 { sd->spamcount_SR_LIGHTNINGWALK = sd->k_tick_c; return 0; }                 sd->spamcount_SR_LIGHTNINGWALK = 0;                 sd->spamtick_SR_LIGHTNINGWALK = tick + sd->kdelay;                 break;
			case SR_KNUCKLEARROW:                  if (k_tick_check(sd, sd->spamtick_SR_KNUCKLEARROW,                  sd->spamcount_SR_KNUCKLEARROW,                  battle_config.kd_SR_KNUCKLEARROW,                  battle_config.kdw_SR_KNUCKLEARROW))                  { sd->spamcount_SR_KNUCKLEARROW = sd->k_tick_c; return 0; }                  sd->spamcount_SR_KNUCKLEARROW = 0;                  sd->spamtick_SR_KNUCKLEARROW = tick + sd->kdelay;                  break;
			case SR_WINDMILL:                      if (k_tick_check(sd, sd->spamtick_SR_WINDMILL,                      sd->spamcount_SR_WINDMILL,                      battle_config.kd_SR_WINDMILL,                      battle_config.kdw_SR_WINDMILL))                      { sd->spamcount_SR_WINDMILL = sd->k_tick_c; return 0; }                      sd->spamcount_SR_WINDMILL = 0;                      sd->spamtick_SR_WINDMILL = tick + sd->kdelay;                      break;
			case SR_RAISINGDRAGON:                 if (k_tick_check(sd, sd->spamtick_SR_RAISINGDRAGON,                 sd->spamcount_SR_RAISINGDRAGON,                 battle_config.kd_SR_RAISINGDRAGON,                 battle_config.kdw_SR_RAISINGDRAGON))                 { sd->spamcount_SR_RAISINGDRAGON = sd->k_tick_c; return 0; }                 sd->spamcount_SR_RAISINGDRAGON = 0;                 sd->spamtick_SR_RAISINGDRAGON = tick + sd->kdelay;                 break;
			case SR_GENTLETOUCH:                   if (k_tick_check(sd, sd->spamtick_SR_GENTLETOUCH,                   sd->spamcount_SR_GENTLETOUCH,                   battle_config.kd_SR_GENTLETOUCH,                   battle_config.kdw_SR_GENTLETOUCH))                   { sd->spamcount_SR_GENTLETOUCH = sd->k_tick_c; return 0; }                   sd->spamcount_SR_GENTLETOUCH = 0;                   sd->spamtick_SR_GENTLETOUCH = tick + sd->kdelay;                   break;
			case SR_ASSIMILATEPOWER:               if (k_tick_check(sd, sd->spamtick_SR_ASSIMILATEPOWER,               sd->spamcount_SR_ASSIMILATEPOWER,               battle_config.kd_SR_ASSIMILATEPOWER,               battle_config.kdw_SR_ASSIMILATEPOWER))               { sd->spamcount_SR_ASSIMILATEPOWER = sd->k_tick_c; return 0; }               sd->spamcount_SR_ASSIMILATEPOWER = 0;               sd->spamtick_SR_ASSIMILATEPOWER = tick + sd->kdelay;               break;
			case SR_POWERVELOCITY:                 if (k_tick_check(sd, sd->spamtick_SR_POWERVELOCITY,                 sd->spamcount_SR_POWERVELOCITY,                 battle_config.kd_SR_POWERVELOCITY,                 battle_config.kdw_SR_POWERVELOCITY))                 { sd->spamcount_SR_POWERVELOCITY = sd->k_tick_c; return 0; }                 sd->spamcount_SR_POWERVELOCITY = 0;                 sd->spamtick_SR_POWERVELOCITY = tick + sd->kdelay;                 break;
			case SR_CRESCENTELBOW_AUTOSPELL:       if (k_tick_check(sd, sd->spamtick_SR_CRESCENTELBOW_AUTOSPELL,       sd->spamcount_SR_CRESCENTELBOW_AUTOSPELL,       battle_config.kd_SR_CRESCENTELBOW_AUTOSPELL,       battle_config.kdw_SR_CRESCENTELBOW_AUTOSPELL))       { sd->spamcount_SR_CRESCENTELBOW_AUTOSPELL = sd->k_tick_c; return 0; }       sd->spamcount_SR_CRESCENTELBOW_AUTOSPELL = 0;       sd->spamtick_SR_CRESCENTELBOW_AUTOSPELL = tick + sd->kdelay;       break;
			case SR_GATEOFHELL:                    if (k_tick_check(sd, sd->spamtick_SR_GATEOFHELL,                    sd->spamcount_SR_GATEOFHELL,                    battle_config.kd_SR_GATEOFHELL,                    battle_config.kdw_SR_GATEOFHELL))                    { sd->spamcount_SR_GATEOFHELL = sd->k_tick_c; return 0; }                    sd->spamcount_SR_GATEOFHELL = 0;                    sd->spamtick_SR_GATEOFHELL = tick + sd->kdelay;                    break;
			case SR_GENTLETOUCH_QUIET:             if (k_tick_check(sd, sd->spamtick_SR_GENTLETOUCH_QUIET,             sd->spamcount_SR_GENTLETOUCH_QUIET,             battle_config.kd_SR_GENTLETOUCH_QUIET,             battle_config.kdw_SR_GENTLETOUCH_QUIET))             { sd->spamcount_SR_GENTLETOUCH_QUIET = sd->k_tick_c; return 0; }             sd->spamcount_SR_GENTLETOUCH_QUIET = 0;             sd->spamtick_SR_GENTLETOUCH_QUIET = tick + sd->kdelay;             break;
			case SR_GENTLETOUCH_CURE:              if (k_tick_check(sd, sd->spamtick_SR_GENTLETOUCH_CURE,              sd->spamcount_SR_GENTLETOUCH_CURE,              battle_config.kd_SR_GENTLETOUCH_CURE,              battle_config.kdw_SR_GENTLETOUCH_CURE))              { sd->spamcount_SR_GENTLETOUCH_CURE = sd->k_tick_c; return 0; }              sd->spamcount_SR_GENTLETOUCH_CURE = 0;              sd->spamtick_SR_GENTLETOUCH_CURE = tick + sd->kdelay;              break;
			case SR_GENTLETOUCH_ENERGYGAIN:        if (k_tick_check(sd, sd->spamtick_SR_GENTLETOUCH_ENERGYGAIN,        sd->spamcount_SR_GENTLETOUCH_ENERGYGAIN,        battle_config.kd_SR_GENTLETOUCH_ENERGYGAIN,        battle_config.kdw_SR_GENTLETOUCH_ENERGYGAIN))        { sd->spamcount_SR_GENTLETOUCH_ENERGYGAIN = sd->k_tick_c; return 0; }        sd->spamcount_SR_GENTLETOUCH_ENERGYGAIN = 0;        sd->spamtick_SR_GENTLETOUCH_ENERGYGAIN = tick + sd->kdelay;        break;
			case SR_GENTLETOUCH_CHANGE:            if (k_tick_check(sd, sd->spamtick_SR_GENTLETOUCH_CHANGE,            sd->spamcount_SR_GENTLETOUCH_CHANGE,            battle_config.kd_SR_GENTLETOUCH_CHANGE,            battle_config.kdw_SR_GENTLETOUCH_CHANGE))            { sd->spamcount_SR_GENTLETOUCH_CHANGE = sd->k_tick_c; return 0; }            sd->spamcount_SR_GENTLETOUCH_CHANGE = 0;            sd->spamtick_SR_GENTLETOUCH_CHANGE = tick + sd->kdelay;            break;
			case SR_GENTLETOUCH_REVITALIZE:        if (k_tick_check(sd, sd->spamtick_SR_GENTLETOUCH_REVITALIZE,        sd->spamcount_SR_GENTLETOUCH_REVITALIZE,        battle_config.kd_SR_GENTLETOUCH_REVITALIZE,        battle_config.kdw_SR_GENTLETOUCH_REVITALIZE))        { sd->spamcount_SR_GENTLETOUCH_REVITALIZE = sd->k_tick_c; return 0; }        sd->spamcount_SR_GENTLETOUCH_REVITALIZE = 0;        sd->spamtick_SR_GENTLETOUCH_REVITALIZE = tick + sd->kdelay;        break;
			case WA_SWING_DANCE:                   if (k_tick_check(sd, sd->spamtick_WA_SWING_DANCE,                   sd->spamcount_WA_SWING_DANCE,                   battle_config.kd_WA_SWING_DANCE,                   battle_config.kdw_WA_SWING_DANCE))                   { sd->spamcount_WA_SWING_DANCE = sd->k_tick_c; return 0; }                   sd->spamcount_WA_SWING_DANCE = 0;                   sd->spamtick_WA_SWING_DANCE = tick + sd->kdelay;                   break;
			case WA_SYMPHONY_OF_LOVER:             if (k_tick_check(sd, sd->spamtick_WA_SYMPHONY_OF_LOVER,             sd->spamcount_WA_SYMPHONY_OF_LOVER,             battle_config.kd_WA_SYMPHONY_OF_LOVER,             battle_config.kdw_WA_SYMPHONY_OF_LOVER))             { sd->spamcount_WA_SYMPHONY_OF_LOVER = sd->k_tick_c; return 0; }             sd->spamcount_WA_SYMPHONY_OF_LOVER = 0;             sd->spamtick_WA_SYMPHONY_OF_LOVER = tick + sd->kdelay;             break;
			case WA_MOONLIT_SERENADE:              if (k_tick_check(sd, sd->spamtick_WA_MOONLIT_SERENADE,              sd->spamcount_WA_MOONLIT_SERENADE,              battle_config.kd_WA_MOONLIT_SERENADE,              battle_config.kdw_WA_MOONLIT_SERENADE))              { sd->spamcount_WA_MOONLIT_SERENADE = sd->k_tick_c; return 0; }              sd->spamcount_WA_MOONLIT_SERENADE = 0;              sd->spamtick_WA_MOONLIT_SERENADE = tick + sd->kdelay;              break;
			case MI_RUSH_WINDMILL:                 if (k_tick_check(sd, sd->spamtick_MI_RUSH_WINDMILL,                 sd->spamcount_MI_RUSH_WINDMILL,                 battle_config.kd_MI_RUSH_WINDMILL,                 battle_config.kdw_MI_RUSH_WINDMILL))                 { sd->spamcount_MI_RUSH_WINDMILL = sd->k_tick_c; return 0; }                 sd->spamcount_MI_RUSH_WINDMILL = 0;                 sd->spamtick_MI_RUSH_WINDMILL = tick + sd->kdelay;                 break;
			case MI_ECHOSONG:                      if (k_tick_check(sd, sd->spamtick_MI_ECHOSONG,                      sd->spamcount_MI_ECHOSONG,                      battle_config.kd_MI_ECHOSONG,                      battle_config.kdw_MI_ECHOSONG))                      { sd->spamcount_MI_ECHOSONG = sd->k_tick_c; return 0; }                      sd->spamcount_MI_ECHOSONG = 0;                      sd->spamtick_MI_ECHOSONG = tick + sd->kdelay;                      break;
			case MI_HARMONIZE:                     if (k_tick_check(sd, sd->spamtick_MI_HARMONIZE,                     sd->spamcount_MI_HARMONIZE,                     battle_config.kd_MI_HARMONIZE,                     battle_config.kdw_MI_HARMONIZE))                     { sd->spamcount_MI_HARMONIZE = sd->k_tick_c; return 0; }                     sd->spamcount_MI_HARMONIZE = 0;                     sd->spamtick_MI_HARMONIZE = tick + sd->kdelay;                     break;
			case WM_LESSON:                        if (k_tick_check(sd, sd->spamtick_WM_LESSON,                        sd->spamcount_WM_LESSON,                        battle_config.kd_WM_LESSON,                        battle_config.kdw_WM_LESSON))                        { sd->spamcount_WM_LESSON = sd->k_tick_c; return 0; }                        sd->spamcount_WM_LESSON = 0;                        sd->spamtick_WM_LESSON = tick + sd->kdelay;                        break;
			case WM_METALICSOUND:                  if (k_tick_check(sd, sd->spamtick_WM_METALICSOUND,                  sd->spamcount_WM_METALICSOUND,                  battle_config.kd_WM_METALICSOUND,                  battle_config.kdw_WM_METALICSOUND))                  { sd->spamcount_WM_METALICSOUND = sd->k_tick_c; return 0; }                  sd->spamcount_WM_METALICSOUND = 0;                  sd->spamtick_WM_METALICSOUND = tick + sd->kdelay;                  break;
			case WM_REVERBERATION:                 if (k_tick_check(sd, sd->spamtick_WM_REVERBERATION,                 sd->spamcount_WM_REVERBERATION,                 battle_config.kd_WM_REVERBERATION,                 battle_config.kdw_WM_REVERBERATION))                 { sd->spamcount_WM_REVERBERATION = sd->k_tick_c; return 0; }                 sd->spamcount_WM_REVERBERATION = 0;                 sd->spamtick_WM_REVERBERATION = tick + sd->kdelay;                 break;
			case WM_REVERBERATION_MELEE:           if (k_tick_check(sd, sd->spamtick_WM_REVERBERATION_MELEE,           sd->spamcount_WM_REVERBERATION_MELEE,           battle_config.kd_WM_REVERBERATION_MELEE,           battle_config.kdw_WM_REVERBERATION_MELEE))           { sd->spamcount_WM_REVERBERATION_MELEE = sd->k_tick_c; return 0; }           sd->spamcount_WM_REVERBERATION_MELEE = 0;           sd->spamtick_WM_REVERBERATION_MELEE = tick + sd->kdelay;           break;
			case WM_REVERBERATION_MAGIC:           if (k_tick_check(sd, sd->spamtick_WM_REVERBERATION_MAGIC,           sd->spamcount_WM_REVERBERATION_MAGIC,           battle_config.kd_WM_REVERBERATION_MAGIC,           battle_config.kdw_WM_REVERBERATION_MAGIC))           { sd->spamcount_WM_REVERBERATION_MAGIC = sd->k_tick_c; return 0; }           sd->spamcount_WM_REVERBERATION_MAGIC = 0;           sd->spamtick_WM_REVERBERATION_MAGIC = tick + sd->kdelay;           break;
			case WM_DOMINION_IMPULSE:              if (k_tick_check(sd, sd->spamtick_WM_DOMINION_IMPULSE,              sd->spamcount_WM_DOMINION_IMPULSE,              battle_config.kd_WM_DOMINION_IMPULSE,              battle_config.kdw_WM_DOMINION_IMPULSE))              { sd->spamcount_WM_DOMINION_IMPULSE = sd->k_tick_c; return 0; }              sd->spamcount_WM_DOMINION_IMPULSE = 0;              sd->spamtick_WM_DOMINION_IMPULSE = tick + sd->kdelay;              break;
			case WM_SEVERE_RAINSTORM:              if (k_tick_check(sd, sd->spamtick_WM_SEVERE_RAINSTORM,              sd->spamcount_WM_SEVERE_RAINSTORM,              battle_config.kd_WM_SEVERE_RAINSTORM,              battle_config.kdw_WM_SEVERE_RAINSTORM))              { sd->spamcount_WM_SEVERE_RAINSTORM = sd->k_tick_c; return 0; }              sd->spamcount_WM_SEVERE_RAINSTORM = 0;              sd->spamtick_WM_SEVERE_RAINSTORM = tick + sd->kdelay;              break;
			case WM_SEVERE_RAINSTORM_MELEE:        if (k_tick_check(sd, sd->spamtick_WM_SEVERE_RAINSTORM_MELEE,        sd->spamcount_WM_SEVERE_RAINSTORM_MELEE,        battle_config.kd_WM_SEVERE_RAINSTORM_MELEE,        battle_config.kdw_WM_SEVERE_RAINSTORM_MELEE))        { sd->spamcount_WM_SEVERE_RAINSTORM_MELEE = sd->k_tick_c; return 0; }        sd->spamcount_WM_SEVERE_RAINSTORM_MELEE = 0;        sd->spamtick_WM_SEVERE_RAINSTORM_MELEE = tick + sd->kdelay;        break;
			case WM_POEMOFNETHERWORLD:             if (k_tick_check(sd, sd->spamtick_WM_POEMOFNETHERWORLD,             sd->spamcount_WM_POEMOFNETHERWORLD,             battle_config.kd_WM_POEMOFNETHERWORLD,             battle_config.kdw_WM_POEMOFNETHERWORLD))             { sd->spamcount_WM_POEMOFNETHERWORLD = sd->k_tick_c; return 0; }             sd->spamcount_WM_POEMOFNETHERWORLD = 0;             sd->spamtick_WM_POEMOFNETHERWORLD = tick + sd->kdelay;             break;
			case WM_VOICEOFSIREN:                  if (k_tick_check(sd, sd->spamtick_WM_VOICEOFSIREN,                  sd->spamcount_WM_VOICEOFSIREN,                  battle_config.kd_WM_VOICEOFSIREN,                  battle_config.kdw_WM_VOICEOFSIREN))                  { sd->spamcount_WM_VOICEOFSIREN = sd->k_tick_c; return 0; }                  sd->spamcount_WM_VOICEOFSIREN = 0;                  sd->spamtick_WM_VOICEOFSIREN = tick + sd->kdelay;                  break;
			case WM_DEADHILLHERE:                  if (k_tick_check(sd, sd->spamtick_WM_DEADHILLHERE,                  sd->spamcount_WM_DEADHILLHERE,                  battle_config.kd_WM_DEADHILLHERE,                  battle_config.kdw_WM_DEADHILLHERE))                  { sd->spamcount_WM_DEADHILLHERE = sd->k_tick_c; return 0; }                  sd->spamcount_WM_DEADHILLHERE = 0;                  sd->spamtick_WM_DEADHILLHERE = tick + sd->kdelay;                  break;
			case WM_LULLABY_DEEPSLEEP:             if (k_tick_check(sd, sd->spamtick_WM_LULLABY_DEEPSLEEP,             sd->spamcount_WM_LULLABY_DEEPSLEEP,             battle_config.kd_WM_LULLABY_DEEPSLEEP,             battle_config.kdw_WM_LULLABY_DEEPSLEEP))             { sd->spamcount_WM_LULLABY_DEEPSLEEP = sd->k_tick_c; return 0; }             sd->spamcount_WM_LULLABY_DEEPSLEEP = 0;             sd->spamtick_WM_LULLABY_DEEPSLEEP = tick + sd->kdelay;             break;
			case WM_SIRCLEOFNATURE:                if (k_tick_check(sd, sd->spamtick_WM_SIRCLEOFNATURE,                sd->spamcount_WM_SIRCLEOFNATURE,                battle_config.kd_WM_SIRCLEOFNATURE,                battle_config.kdw_WM_SIRCLEOFNATURE))                { sd->spamcount_WM_SIRCLEOFNATURE = sd->k_tick_c; return 0; }                sd->spamcount_WM_SIRCLEOFNATURE = 0;                sd->spamtick_WM_SIRCLEOFNATURE = tick + sd->kdelay;                break;
			case WM_RANDOMIZESPELL:                if (k_tick_check(sd, sd->spamtick_WM_RANDOMIZESPELL,                sd->spamcount_WM_RANDOMIZESPELL,                battle_config.kd_WM_RANDOMIZESPELL,                battle_config.kdw_WM_RANDOMIZESPELL))                { sd->spamcount_WM_RANDOMIZESPELL = sd->k_tick_c; return 0; }                sd->spamcount_WM_RANDOMIZESPELL = 0;                sd->spamtick_WM_RANDOMIZESPELL = tick + sd->kdelay;                break;
			case WM_GLOOMYDAY:                     if (k_tick_check(sd, sd->spamtick_WM_GLOOMYDAY,                     sd->spamcount_WM_GLOOMYDAY,                     battle_config.kd_WM_GLOOMYDAY,                     battle_config.kdw_WM_GLOOMYDAY))                     { sd->spamcount_WM_GLOOMYDAY = sd->k_tick_c; return 0; }                     sd->spamcount_WM_GLOOMYDAY = 0;                     sd->spamtick_WM_GLOOMYDAY = tick + sd->kdelay;                     break;
			case WM_GREAT_ECHO:                    if (k_tick_check(sd, sd->spamtick_WM_GREAT_ECHO,                    sd->spamcount_WM_GREAT_ECHO,                    battle_config.kd_WM_GREAT_ECHO,                    battle_config.kdw_WM_GREAT_ECHO))                    { sd->spamcount_WM_GREAT_ECHO = sd->k_tick_c; return 0; }                    sd->spamcount_WM_GREAT_ECHO = 0;                    sd->spamtick_WM_GREAT_ECHO = tick + sd->kdelay;                    break;
			case WM_SONG_OF_MANA:                  if (k_tick_check(sd, sd->spamtick_WM_SONG_OF_MANA,                  sd->spamcount_WM_SONG_OF_MANA,                  battle_config.kd_WM_SONG_OF_MANA,                  battle_config.kdw_WM_SONG_OF_MANA))                  { sd->spamcount_WM_SONG_OF_MANA = sd->k_tick_c; return 0; }                  sd->spamcount_WM_SONG_OF_MANA = 0;                  sd->spamtick_WM_SONG_OF_MANA = tick + sd->kdelay;                  break;
			case WM_DANCE_WITH_WUG:                if (k_tick_check(sd, sd->spamtick_WM_DANCE_WITH_WUG,                sd->spamcount_WM_DANCE_WITH_WUG,                battle_config.kd_WM_DANCE_WITH_WUG,                battle_config.kdw_WM_DANCE_WITH_WUG))                { sd->spamcount_WM_DANCE_WITH_WUG = sd->k_tick_c; return 0; }                sd->spamcount_WM_DANCE_WITH_WUG = 0;                sd->spamtick_WM_DANCE_WITH_WUG = tick + sd->kdelay;                break;
			case WM_SOUND_OF_DESTRUCTION:          if (k_tick_check(sd, sd->spamtick_WM_SOUND_OF_DESTRUCTION,          sd->spamcount_WM_SOUND_OF_DESTRUCTION,          battle_config.kd_WM_SOUND_OF_DESTRUCTION,          battle_config.kdw_WM_SOUND_OF_DESTRUCTION))          { sd->spamcount_WM_SOUND_OF_DESTRUCTION = sd->k_tick_c; return 0; }          sd->spamcount_WM_SOUND_OF_DESTRUCTION = 0;          sd->spamtick_WM_SOUND_OF_DESTRUCTION = tick + sd->kdelay;          break;
			case WM_SATURDAY_NIGHT_FEVER:          if (k_tick_check(sd, sd->spamtick_WM_SATURDAY_NIGHT_FEVER,          sd->spamcount_WM_SATURDAY_NIGHT_FEVER,          battle_config.kd_WM_SATURDAY_NIGHT_FEVER,          battle_config.kdw_WM_SATURDAY_NIGHT_FEVER))          { sd->spamcount_WM_SATURDAY_NIGHT_FEVER = sd->k_tick_c; return 0; }          sd->spamcount_WM_SATURDAY_NIGHT_FEVER = 0;          sd->spamtick_WM_SATURDAY_NIGHT_FEVER = tick + sd->kdelay;          break;
			case WM_LERADS_DEW:                    if (k_tick_check(sd, sd->spamtick_WM_LERADS_DEW,                    sd->spamcount_WM_LERADS_DEW,                    battle_config.kd_WM_LERADS_DEW,                    battle_config.kdw_WM_LERADS_DEW))                    { sd->spamcount_WM_LERADS_DEW = sd->k_tick_c; return 0; }                    sd->spamcount_WM_LERADS_DEW = 0;                    sd->spamtick_WM_LERADS_DEW = tick + sd->kdelay;                    break;
			case WM_MELODYOFSINK:                  if (k_tick_check(sd, sd->spamtick_WM_MELODYOFSINK,                  sd->spamcount_WM_MELODYOFSINK,                  battle_config.kd_WM_MELODYOFSINK,                  battle_config.kdw_WM_MELODYOFSINK))                  { sd->spamcount_WM_MELODYOFSINK = sd->k_tick_c; return 0; }                  sd->spamcount_WM_MELODYOFSINK = 0;                  sd->spamtick_WM_MELODYOFSINK = tick + sd->kdelay;                  break;
			case WM_BEYOND_OF_WARCRY:              if (k_tick_check(sd, sd->spamtick_WM_BEYOND_OF_WARCRY,              sd->spamcount_WM_BEYOND_OF_WARCRY,              battle_config.kd_WM_BEYOND_OF_WARCRY,              battle_config.kdw_WM_BEYOND_OF_WARCRY))              { sd->spamcount_WM_BEYOND_OF_WARCRY = sd->k_tick_c; return 0; }              sd->spamcount_WM_BEYOND_OF_WARCRY = 0;              sd->spamtick_WM_BEYOND_OF_WARCRY = tick + sd->kdelay;              break;
			case WM_UNLIMITED_HUMMING_VOICE:       if (k_tick_check(sd, sd->spamtick_WM_UNLIMITED_HUMMING_VOICE,       sd->spamcount_WM_UNLIMITED_HUMMING_VOICE,       battle_config.kd_WM_UNLIMITED_HUMMING_VOICE,       battle_config.kdw_WM_UNLIMITED_HUMMING_VOICE))       { sd->spamcount_WM_UNLIMITED_HUMMING_VOICE = sd->k_tick_c; return 0; }       sd->spamcount_WM_UNLIMITED_HUMMING_VOICE = 0;       sd->spamtick_WM_UNLIMITED_HUMMING_VOICE = tick + sd->kdelay;       break;
			case SO_FIREWALK:                      if (k_tick_check(sd, sd->spamtick_SO_FIREWALK,                      sd->spamcount_SO_FIREWALK,                      battle_config.kd_SO_FIREWALK,                      battle_config.kdw_SO_FIREWALK))                      { sd->spamcount_SO_FIREWALK = sd->k_tick_c; return 0; }                      sd->spamcount_SO_FIREWALK = 0;                      sd->spamtick_SO_FIREWALK = tick + sd->kdelay;                      break;
			case SO_ELECTRICWALK:                  if (k_tick_check(sd, sd->spamtick_SO_ELECTRICWALK,                  sd->spamcount_SO_ELECTRICWALK,                  battle_config.kd_SO_ELECTRICWALK,                  battle_config.kdw_SO_ELECTRICWALK))                  { sd->spamcount_SO_ELECTRICWALK = sd->k_tick_c; return 0; }                  sd->spamcount_SO_ELECTRICWALK = 0;                  sd->spamtick_SO_ELECTRICWALK = tick + sd->kdelay;                  break;
			case SO_SPELLFIST:                     if (k_tick_check(sd, sd->spamtick_SO_SPELLFIST,                     sd->spamcount_SO_SPELLFIST,                     battle_config.kd_SO_SPELLFIST,                     battle_config.kdw_SO_SPELLFIST))                     { sd->spamcount_SO_SPELLFIST = sd->k_tick_c; return 0; }                     sd->spamcount_SO_SPELLFIST = 0;                     sd->spamtick_SO_SPELLFIST = tick + sd->kdelay;                     break;
			case SO_EARTHGRAVE:                    if (k_tick_check(sd, sd->spamtick_SO_EARTHGRAVE,                    sd->spamcount_SO_EARTHGRAVE,                    battle_config.kd_SO_EARTHGRAVE,                    battle_config.kdw_SO_EARTHGRAVE))                    { sd->spamcount_SO_EARTHGRAVE = sd->k_tick_c; return 0; }                    sd->spamcount_SO_EARTHGRAVE = 0;                    sd->spamtick_SO_EARTHGRAVE = tick + sd->kdelay;                    break;
			case SO_DIAMONDDUST:                   if (k_tick_check(sd, sd->spamtick_SO_DIAMONDDUST,                   sd->spamcount_SO_DIAMONDDUST,                   battle_config.kd_SO_DIAMONDDUST,                   battle_config.kdw_SO_DIAMONDDUST))                   { sd->spamcount_SO_DIAMONDDUST = sd->k_tick_c; return 0; }                   sd->spamcount_SO_DIAMONDDUST = 0;                   sd->spamtick_SO_DIAMONDDUST = tick + sd->kdelay;                   break;
			case SO_POISON_BUSTER:                 if (k_tick_check(sd, sd->spamtick_SO_POISON_BUSTER,                 sd->spamcount_SO_POISON_BUSTER,                 battle_config.kd_SO_POISON_BUSTER,                 battle_config.kdw_SO_POISON_BUSTER))                 { sd->spamcount_SO_POISON_BUSTER = sd->k_tick_c; return 0; }                 sd->spamcount_SO_POISON_BUSTER = 0;                 sd->spamtick_SO_POISON_BUSTER = tick + sd->kdelay;                 break;
			case SO_PSYCHIC_WAVE:                  if (k_tick_check(sd, sd->spamtick_SO_PSYCHIC_WAVE,                  sd->spamcount_SO_PSYCHIC_WAVE,                  battle_config.kd_SO_PSYCHIC_WAVE,                  battle_config.kdw_SO_PSYCHIC_WAVE))                  { sd->spamcount_SO_PSYCHIC_WAVE = sd->k_tick_c; return 0; }                  sd->spamcount_SO_PSYCHIC_WAVE = 0;                  sd->spamtick_SO_PSYCHIC_WAVE = tick + sd->kdelay;                  break;
			case SO_CLOUD_KILL:                    if (k_tick_check(sd, sd->spamtick_SO_CLOUD_KILL,                    sd->spamcount_SO_CLOUD_KILL,                    battle_config.kd_SO_CLOUD_KILL,                    battle_config.kdw_SO_CLOUD_KILL))                    { sd->spamcount_SO_CLOUD_KILL = sd->k_tick_c; return 0; }                    sd->spamcount_SO_CLOUD_KILL = 0;                    sd->spamtick_SO_CLOUD_KILL = tick + sd->kdelay;                    break;
			case SO_STRIKING:                      if (k_tick_check(sd, sd->spamtick_SO_STRIKING,                      sd->spamcount_SO_STRIKING,                      battle_config.kd_SO_STRIKING,                      battle_config.kdw_SO_STRIKING))                      { sd->spamcount_SO_STRIKING = sd->k_tick_c; return 0; }                      sd->spamcount_SO_STRIKING = 0;                      sd->spamtick_SO_STRIKING = tick + sd->kdelay;                      break;
			case SO_WARMER:                        if (k_tick_check(sd, sd->spamtick_SO_WARMER,                        sd->spamcount_SO_WARMER,                        battle_config.kd_SO_WARMER,                        battle_config.kdw_SO_WARMER))                        { sd->spamcount_SO_WARMER = sd->k_tick_c; return 0; }                        sd->spamcount_SO_WARMER = 0;                        sd->spamtick_SO_WARMER = tick + sd->kdelay;                        break;
			case SO_VACUUM_EXTREME:                if (k_tick_check(sd, sd->spamtick_SO_VACUUM_EXTREME,                sd->spamcount_SO_VACUUM_EXTREME,                battle_config.kd_SO_VACUUM_EXTREME,                battle_config.kdw_SO_VACUUM_EXTREME))                { sd->spamcount_SO_VACUUM_EXTREME = sd->k_tick_c; return 0; }                sd->spamcount_SO_VACUUM_EXTREME = 0;                sd->spamtick_SO_VACUUM_EXTREME = tick + sd->kdelay;                break;
			case SO_VARETYR_SPEAR:                 if (k_tick_check(sd, sd->spamtick_SO_VARETYR_SPEAR,                 sd->spamcount_SO_VARETYR_SPEAR,                 battle_config.kd_SO_VARETYR_SPEAR,                 battle_config.kdw_SO_VARETYR_SPEAR))                 { sd->spamcount_SO_VARETYR_SPEAR = sd->k_tick_c; return 0; }                 sd->spamcount_SO_VARETYR_SPEAR = 0;                 sd->spamtick_SO_VARETYR_SPEAR = tick + sd->kdelay;                 break;
			case SO_ARRULLO:                       if (k_tick_check(sd, sd->spamtick_SO_ARRULLO,                       sd->spamcount_SO_ARRULLO,                       battle_config.kd_SO_ARRULLO,                       battle_config.kdw_SO_ARRULLO))                       { sd->spamcount_SO_ARRULLO = sd->k_tick_c; return 0; }                       sd->spamcount_SO_ARRULLO = 0;                       sd->spamtick_SO_ARRULLO = tick + sd->kdelay;                       break;
			case SO_EL_CONTROL:                    if (k_tick_check(sd, sd->spamtick_SO_EL_CONTROL,                    sd->spamcount_SO_EL_CONTROL,                    battle_config.kd_SO_EL_CONTROL,                    battle_config.kdw_SO_EL_CONTROL))                    { sd->spamcount_SO_EL_CONTROL = sd->k_tick_c; return 0; }                    sd->spamcount_SO_EL_CONTROL = 0;                    sd->spamtick_SO_EL_CONTROL = tick + sd->kdelay;                    break;
			case SO_EL_ACTION:                     if (k_tick_check(sd, sd->spamtick_SO_EL_ACTION,                     sd->spamcount_SO_EL_ACTION,                     battle_config.kd_SO_EL_ACTION,                     battle_config.kdw_SO_EL_ACTION))                     { sd->spamcount_SO_EL_ACTION = sd->k_tick_c; return 0; }                     sd->spamcount_SO_EL_ACTION = 0;                     sd->spamtick_SO_EL_ACTION = tick + sd->kdelay;                     break;
			case SO_EL_ANALYSIS:                   if (k_tick_check(sd, sd->spamtick_SO_EL_ANALYSIS,                   sd->spamcount_SO_EL_ANALYSIS,                   battle_config.kd_SO_EL_ANALYSIS,                   battle_config.kdw_SO_EL_ANALYSIS))                   { sd->spamcount_SO_EL_ANALYSIS = sd->k_tick_c; return 0; }                   sd->spamcount_SO_EL_ANALYSIS = 0;                   sd->spamtick_SO_EL_ANALYSIS = tick + sd->kdelay;                   break;
			case SO_EL_SYMPATHY:                   if (k_tick_check(sd, sd->spamtick_SO_EL_SYMPATHY,                   sd->spamcount_SO_EL_SYMPATHY,                   battle_config.kd_SO_EL_SYMPATHY,                   battle_config.kdw_SO_EL_SYMPATHY))                   { sd->spamcount_SO_EL_SYMPATHY = sd->k_tick_c; return 0; }                   sd->spamcount_SO_EL_SYMPATHY = 0;                   sd->spamtick_SO_EL_SYMPATHY = tick + sd->kdelay;                   break;
			case SO_EL_CURE:                       if (k_tick_check(sd, sd->spamtick_SO_EL_CURE,                       sd->spamcount_SO_EL_CURE,                       battle_config.kd_SO_EL_CURE,                       battle_config.kdw_SO_EL_CURE))                       { sd->spamcount_SO_EL_CURE = sd->k_tick_c; return 0; }                       sd->spamcount_SO_EL_CURE = 0;                       sd->spamtick_SO_EL_CURE = tick + sd->kdelay;                       break;
			case GN_CART_TORNADO:                  if (k_tick_check(sd, sd->spamtick_GN_CART_TORNADO,                  sd->spamcount_GN_CART_TORNADO,                  battle_config.kd_GN_CART_TORNADO,                  battle_config.kdw_GN_CART_TORNADO))                  { sd->spamcount_GN_CART_TORNADO = sd->k_tick_c; return 0; }                  sd->spamcount_GN_CART_TORNADO = 0;                  sd->spamtick_GN_CART_TORNADO = tick + sd->kdelay;                  break;
			case GN_CARTCANNON:                    if (k_tick_check(sd, sd->spamtick_GN_CARTCANNON,                    sd->spamcount_GN_CARTCANNON,                    battle_config.kd_GN_CARTCANNON,                    battle_config.kdw_GN_CARTCANNON))                    { sd->spamcount_GN_CARTCANNON = sd->k_tick_c; return 0; }                    sd->spamcount_GN_CARTCANNON = 0;                    sd->spamtick_GN_CARTCANNON = tick + sd->kdelay;                    break;
			case GN_THORNS_TRAP:                   if (k_tick_check(sd, sd->spamtick_GN_THORNS_TRAP,                   sd->spamcount_GN_THORNS_TRAP,                   battle_config.kd_GN_THORNS_TRAP,                   battle_config.kdw_GN_THORNS_TRAP))                   { sd->spamcount_GN_THORNS_TRAP = sd->k_tick_c; return 0; }                   sd->spamcount_GN_THORNS_TRAP = 0;                   sd->spamtick_GN_THORNS_TRAP = tick + sd->kdelay;                   break;
			case GN_BLOOD_SUCKER:                  if (k_tick_check(sd, sd->spamtick_GN_BLOOD_SUCKER,                  sd->spamcount_GN_BLOOD_SUCKER,                  battle_config.kd_GN_BLOOD_SUCKER,                  battle_config.kdw_GN_BLOOD_SUCKER))                  { sd->spamcount_GN_BLOOD_SUCKER = sd->k_tick_c; return 0; }                  sd->spamcount_GN_BLOOD_SUCKER = 0;                  sd->spamtick_GN_BLOOD_SUCKER = tick + sd->kdelay;                  break;
			case GN_SPORE_EXPLOSION:               if (k_tick_check(sd, sd->spamtick_GN_SPORE_EXPLOSION,               sd->spamcount_GN_SPORE_EXPLOSION,               battle_config.kd_GN_SPORE_EXPLOSION,               battle_config.kdw_GN_SPORE_EXPLOSION))               { sd->spamcount_GN_SPORE_EXPLOSION = sd->k_tick_c; return 0; }               sd->spamcount_GN_SPORE_EXPLOSION = 0;               sd->spamtick_GN_SPORE_EXPLOSION = tick + sd->kdelay;               break;
			case GN_WALLOFTHORN:                   if (k_tick_check(sd, sd->spamtick_GN_WALLOFTHORN,                   sd->spamcount_GN_WALLOFTHORN,                   battle_config.kd_GN_WALLOFTHORN,                   battle_config.kdw_GN_WALLOFTHORN))                   { sd->spamcount_GN_WALLOFTHORN = sd->k_tick_c; return 0; }                   sd->spamcount_GN_WALLOFTHORN = 0;                   sd->spamtick_GN_WALLOFTHORN = tick + sd->kdelay;                   break;
			case GN_CRAZYWEED:                     if (k_tick_check(sd, sd->spamtick_GN_CRAZYWEED,                     sd->spamcount_GN_CRAZYWEED,                     battle_config.kd_GN_CRAZYWEED,                     battle_config.kdw_GN_CRAZYWEED))                     { sd->spamcount_GN_CRAZYWEED = sd->k_tick_c; return 0; }                     sd->spamcount_GN_CRAZYWEED = 0;                     sd->spamtick_GN_CRAZYWEED = tick + sd->kdelay;                     break;
			case GN_DEMONIC_FIRE:                  if (k_tick_check(sd, sd->spamtick_GN_DEMONIC_FIRE,                  sd->spamcount_GN_DEMONIC_FIRE,                  battle_config.kd_GN_DEMONIC_FIRE,                  battle_config.kdw_GN_DEMONIC_FIRE))                  { sd->spamcount_GN_DEMONIC_FIRE = sd->k_tick_c; return 0; }                  sd->spamcount_GN_DEMONIC_FIRE = 0;                  sd->spamtick_GN_DEMONIC_FIRE = tick + sd->kdelay;                  break;
			case GN_FIRE_EXPANSION:                if (k_tick_check(sd, sd->spamtick_GN_FIRE_EXPANSION,                sd->spamcount_GN_FIRE_EXPANSION,                battle_config.kd_GN_FIRE_EXPANSION,                battle_config.kdw_GN_FIRE_EXPANSION))                { sd->spamcount_GN_FIRE_EXPANSION = sd->k_tick_c; return 0; }                sd->spamcount_GN_FIRE_EXPANSION = 0;                sd->spamtick_GN_FIRE_EXPANSION = tick + sd->kdelay;                break;
			case GN_HELLS_PLANT:                   if (k_tick_check(sd, sd->spamtick_GN_HELLS_PLANT,                   sd->spamcount_GN_HELLS_PLANT,                   battle_config.kd_GN_HELLS_PLANT,                   battle_config.kdw_GN_HELLS_PLANT))                   { sd->spamcount_GN_HELLS_PLANT = sd->k_tick_c; return 0; }                   sd->spamcount_GN_HELLS_PLANT = 0;                   sd->spamtick_GN_HELLS_PLANT = tick + sd->kdelay;                   break;
			case GN_MANDRAGORA:                    if (k_tick_check(sd, sd->spamtick_GN_MANDRAGORA,                    sd->spamcount_GN_MANDRAGORA,                    battle_config.kd_GN_MANDRAGORA,                    battle_config.kdw_GN_MANDRAGORA))                    { sd->spamcount_GN_MANDRAGORA = sd->k_tick_c; return 0; }                    sd->spamcount_GN_MANDRAGORA = 0;                    sd->spamtick_GN_MANDRAGORA = tick + sd->kdelay;                    break;
			case GN_SLINGITEM:                     if (k_tick_check(sd, sd->spamtick_GN_SLINGITEM,                     sd->spamcount_GN_SLINGITEM,                     battle_config.kd_GN_SLINGITEM,                     battle_config.kdw_GN_SLINGITEM))                     { sd->spamcount_GN_SLINGITEM = sd->k_tick_c; return 0; }                     sd->spamcount_GN_SLINGITEM = 0;                     sd->spamtick_GN_SLINGITEM = tick + sd->kdelay;                     break;
			case GN_CHANGEMATERIAL:                if (k_tick_check(sd, sd->spamtick_GN_CHANGEMATERIAL,                sd->spamcount_GN_CHANGEMATERIAL,                battle_config.kd_GN_CHANGEMATERIAL,                battle_config.kdw_GN_CHANGEMATERIAL))                { sd->spamcount_GN_CHANGEMATERIAL = sd->k_tick_c; return 0; }                sd->spamcount_GN_CHANGEMATERIAL = 0;                sd->spamtick_GN_CHANGEMATERIAL = tick + sd->kdelay;                break;
			case AB_SECRAMENT:                     if (k_tick_check(sd, sd->spamtick_AB_SECRAMENT,                     sd->spamcount_AB_SECRAMENT,                     battle_config.kd_AB_SECRAMENT,                     battle_config.kdw_AB_SECRAMENT))                     { sd->spamcount_AB_SECRAMENT = sd->k_tick_c; return 0; }                     sd->spamcount_AB_SECRAMENT = 0;                     sd->spamtick_AB_SECRAMENT = tick + sd->kdelay;                     break;
			case SR_HOWLINGOFLION:                 if (k_tick_check(sd, sd->spamtick_SR_HOWLINGOFLION,                 sd->spamcount_SR_HOWLINGOFLION,                 battle_config.kd_SR_HOWLINGOFLION,                 battle_config.kdw_SR_HOWLINGOFLION))                 { sd->spamcount_SR_HOWLINGOFLION = sd->k_tick_c; return 0; }                 sd->spamcount_SR_HOWLINGOFLION = 0;                 sd->spamtick_SR_HOWLINGOFLION = tick + sd->kdelay;                 break;
			case SR_RIDEINLIGHTNING:               if (k_tick_check(sd, sd->spamtick_SR_RIDEINLIGHTNING,               sd->spamcount_SR_RIDEINLIGHTNING,               battle_config.kd_SR_RIDEINLIGHTNING,               battle_config.kdw_SR_RIDEINLIGHTNING))               { sd->spamcount_SR_RIDEINLIGHTNING = sd->k_tick_c; return 0; }               sd->spamcount_SR_RIDEINLIGHTNING = 0;               sd->spamtick_SR_RIDEINLIGHTNING = tick + sd->kdelay;               break;
			case LG_OVERBRAND_BRANDISH:            if (k_tick_check(sd, sd->spamtick_LG_OVERBRAND_BRANDISH,            sd->spamcount_LG_OVERBRAND_BRANDISH,            battle_config.kd_LG_OVERBRAND_BRANDISH,            battle_config.kdw_LG_OVERBRAND_BRANDISH))            { sd->spamcount_LG_OVERBRAND_BRANDISH = sd->k_tick_c; return 0; }            sd->spamcount_LG_OVERBRAND_BRANDISH = 0;            sd->spamtick_LG_OVERBRAND_BRANDISH = tick + sd->kdelay;            break;
			case RL_GLITTERING_GREED:              if (k_tick_check(sd, sd->spamtick_RL_GLITTERING_GREED,              sd->spamcount_RL_GLITTERING_GREED,              battle_config.kd_RL_GLITTERING_GREED,              battle_config.kdw_RL_GLITTERING_GREED))              { sd->spamcount_RL_GLITTERING_GREED = sd->k_tick_c; return 0; }              sd->spamcount_RL_GLITTERING_GREED = 0;              sd->spamtick_RL_GLITTERING_GREED = tick + sd->kdelay;              break;
			case RL_RICHS_COIN:                    if (k_tick_check(sd, sd->spamtick_RL_RICHS_COIN,                    sd->spamcount_RL_RICHS_COIN,                    battle_config.kd_RL_RICHS_COIN,                    battle_config.kdw_RL_RICHS_COIN))                    { sd->spamcount_RL_RICHS_COIN = sd->k_tick_c; return 0; }                    sd->spamcount_RL_RICHS_COIN = 0;                    sd->spamtick_RL_RICHS_COIN = tick + sd->kdelay;                    break;
			case RL_MASS_SPIRAL:                   if (k_tick_check(sd, sd->spamtick_RL_MASS_SPIRAL,                   sd->spamcount_RL_MASS_SPIRAL,                   battle_config.kd_RL_MASS_SPIRAL,                   battle_config.kdw_RL_MASS_SPIRAL))                   { sd->spamcount_RL_MASS_SPIRAL = sd->k_tick_c; return 0; }                   sd->spamcount_RL_MASS_SPIRAL = 0;                   sd->spamtick_RL_MASS_SPIRAL = tick + sd->kdelay;                   break;
			case RL_BANISHING_BUSTER:              if (k_tick_check(sd, sd->spamtick_RL_BANISHING_BUSTER,              sd->spamcount_RL_BANISHING_BUSTER,              battle_config.kd_RL_BANISHING_BUSTER,              battle_config.kdw_RL_BANISHING_BUSTER))              { sd->spamcount_RL_BANISHING_BUSTER = sd->k_tick_c; return 0; }              sd->spamcount_RL_BANISHING_BUSTER = 0;              sd->spamtick_RL_BANISHING_BUSTER = tick + sd->kdelay;              break;
			case RL_B_TRAP:                        if (k_tick_check(sd, sd->spamtick_RL_B_TRAP,                        sd->spamcount_RL_B_TRAP,                        battle_config.kd_RL_B_TRAP,                        battle_config.kdw_RL_B_TRAP))                        { sd->spamcount_RL_B_TRAP = sd->k_tick_c; return 0; }                        sd->spamcount_RL_B_TRAP = 0;                        sd->spamtick_RL_B_TRAP = tick + sd->kdelay;                        break;
			case RL_S_STORM:                       if (k_tick_check(sd, sd->spamtick_RL_S_STORM,                       sd->spamcount_RL_S_STORM,                       battle_config.kd_RL_S_STORM,                       battle_config.kdw_RL_S_STORM))                       { sd->spamcount_RL_S_STORM = sd->k_tick_c; return 0; }                       sd->spamcount_RL_S_STORM = 0;                       sd->spamtick_RL_S_STORM = tick + sd->kdelay;                       break;
			case RL_E_CHAIN:                       if (k_tick_check(sd, sd->spamtick_RL_E_CHAIN,                       sd->spamcount_RL_E_CHAIN,                       battle_config.kd_RL_E_CHAIN,                       battle_config.kdw_RL_E_CHAIN))                       { sd->spamcount_RL_E_CHAIN = sd->k_tick_c; return 0; }                       sd->spamcount_RL_E_CHAIN = 0;                       sd->spamtick_RL_E_CHAIN = tick + sd->kdelay;                       break;
			case RL_QD_SHOT:                       if (k_tick_check(sd, sd->spamtick_RL_QD_SHOT,                       sd->spamcount_RL_QD_SHOT,                       battle_config.kd_RL_QD_SHOT,                       battle_config.kdw_RL_QD_SHOT))                       { sd->spamcount_RL_QD_SHOT = sd->k_tick_c; return 0; }                       sd->spamcount_RL_QD_SHOT = 0;                       sd->spamtick_RL_QD_SHOT = tick + sd->kdelay;                       break;
			case RL_C_MARKER:                      if (k_tick_check(sd, sd->spamtick_RL_C_MARKER,                      sd->spamcount_RL_C_MARKER,                      battle_config.kd_RL_C_MARKER,                      battle_config.kdw_RL_C_MARKER))                      { sd->spamcount_RL_C_MARKER = sd->k_tick_c; return 0; }                      sd->spamcount_RL_C_MARKER = 0;                      sd->spamtick_RL_C_MARKER = tick + sd->kdelay;                      break;
			case RL_FIREDANCE:                     if (k_tick_check(sd, sd->spamtick_RL_FIREDANCE,                     sd->spamcount_RL_FIREDANCE,                     battle_config.kd_RL_FIREDANCE,                     battle_config.kdw_RL_FIREDANCE))                     { sd->spamcount_RL_FIREDANCE = sd->k_tick_c; return 0; }                     sd->spamcount_RL_FIREDANCE = 0;                     sd->spamtick_RL_FIREDANCE = tick + sd->kdelay;                     break;
			case RL_H_MINE:                        if (k_tick_check(sd, sd->spamtick_RL_H_MINE,                        sd->spamcount_RL_H_MINE,                        battle_config.kd_RL_H_MINE,                        battle_config.kdw_RL_H_MINE))                        { sd->spamcount_RL_H_MINE = sd->k_tick_c; return 0; }                        sd->spamcount_RL_H_MINE = 0;                        sd->spamtick_RL_H_MINE = tick + sd->kdelay;                        break;
			case RL_P_ALTER:                       if (k_tick_check(sd, sd->spamtick_RL_P_ALTER,                       sd->spamcount_RL_P_ALTER,                       battle_config.kd_RL_P_ALTER,                       battle_config.kdw_RL_P_ALTER))                       { sd->spamcount_RL_P_ALTER = sd->k_tick_c; return 0; }                       sd->spamcount_RL_P_ALTER = 0;                       sd->spamtick_RL_P_ALTER = tick + sd->kdelay;                       break;
			case RL_FALLEN_ANGEL:                  if (k_tick_check(sd, sd->spamtick_RL_FALLEN_ANGEL,                  sd->spamcount_RL_FALLEN_ANGEL,                  battle_config.kd_RL_FALLEN_ANGEL,                  battle_config.kdw_RL_FALLEN_ANGEL))                  { sd->spamcount_RL_FALLEN_ANGEL = sd->k_tick_c; return 0; }                  sd->spamcount_RL_FALLEN_ANGEL = 0;                  sd->spamtick_RL_FALLEN_ANGEL = tick + sd->kdelay;                  break;
			case RL_R_TRIP:                        if (k_tick_check(sd, sd->spamtick_RL_R_TRIP,                        sd->spamcount_RL_R_TRIP,                        battle_config.kd_RL_R_TRIP,                        battle_config.kdw_RL_R_TRIP))                        { sd->spamcount_RL_R_TRIP = sd->k_tick_c; return 0; }                        sd->spamcount_RL_R_TRIP = 0;                        sd->spamtick_RL_R_TRIP = tick + sd->kdelay;                        break;
			case RL_D_TAIL:                        if (k_tick_check(sd, sd->spamtick_RL_D_TAIL,                        sd->spamcount_RL_D_TAIL,                        battle_config.kd_RL_D_TAIL,                        battle_config.kdw_RL_D_TAIL))                        { sd->spamcount_RL_D_TAIL = sd->k_tick_c; return 0; }                        sd->spamcount_RL_D_TAIL = 0;                        sd->spamtick_RL_D_TAIL = tick + sd->kdelay;                        break;
			case RL_FIRE_RAIN:                     if (k_tick_check(sd, sd->spamtick_RL_FIRE_RAIN,                     sd->spamcount_RL_FIRE_RAIN,                     battle_config.kd_RL_FIRE_RAIN,                     battle_config.kdw_RL_FIRE_RAIN))                     { sd->spamcount_RL_FIRE_RAIN = sd->k_tick_c; return 0; }                     sd->spamcount_RL_FIRE_RAIN = 0;                     sd->spamtick_RL_FIRE_RAIN = tick + sd->kdelay;                     break;
			case RL_HEAT_BARREL:                   if (k_tick_check(sd, sd->spamtick_RL_HEAT_BARREL,                   sd->spamcount_RL_HEAT_BARREL,                   battle_config.kd_RL_HEAT_BARREL,                   battle_config.kdw_RL_HEAT_BARREL))                   { sd->spamcount_RL_HEAT_BARREL = sd->k_tick_c; return 0; }                   sd->spamcount_RL_HEAT_BARREL = 0;                   sd->spamtick_RL_HEAT_BARREL = tick + sd->kdelay;                   break;
			case RL_AM_BLAST:                      if (k_tick_check(sd, sd->spamtick_RL_AM_BLAST,                      sd->spamcount_RL_AM_BLAST,                      battle_config.kd_RL_AM_BLAST,                      battle_config.kdw_RL_AM_BLAST))                      { sd->spamcount_RL_AM_BLAST = sd->k_tick_c; return 0; }                      sd->spamcount_RL_AM_BLAST = 0;                      sd->spamtick_RL_AM_BLAST = tick + sd->kdelay;                      break;
			case RL_SLUGSHOT:                      if (k_tick_check(sd, sd->spamtick_RL_SLUGSHOT,                      sd->spamcount_RL_SLUGSHOT,                      battle_config.kd_RL_SLUGSHOT,                      battle_config.kdw_RL_SLUGSHOT))                      { sd->spamcount_RL_SLUGSHOT = sd->k_tick_c; return 0; }                      sd->spamcount_RL_SLUGSHOT = 0;                      sd->spamtick_RL_SLUGSHOT = tick + sd->kdelay;                      break;
			case RL_HAMMER_OF_GOD:                 if (k_tick_check(sd, sd->spamtick_RL_HAMMER_OF_GOD,                 sd->spamcount_RL_HAMMER_OF_GOD,                 battle_config.kd_RL_HAMMER_OF_GOD,                 battle_config.kdw_RL_HAMMER_OF_GOD))                 { sd->spamcount_RL_HAMMER_OF_GOD = sd->k_tick_c; return 0; }                 sd->spamcount_RL_HAMMER_OF_GOD = 0;                 sd->spamtick_RL_HAMMER_OF_GOD = tick + sd->kdelay;                 break;
			case KO_YAMIKUMO:                      if (k_tick_check(sd, sd->spamtick_KO_YAMIKUMO,                      sd->spamcount_KO_YAMIKUMO,                      battle_config.kd_KO_YAMIKUMO,                      battle_config.kdw_KO_YAMIKUMO))                      { sd->spamcount_KO_YAMIKUMO = sd->k_tick_c; return 0; }                      sd->spamcount_KO_YAMIKUMO = 0;                      sd->spamtick_KO_YAMIKUMO = tick + sd->kdelay;                      break;
			case KO_JYUMONJIKIRI:                  if (k_tick_check(sd, sd->spamtick_KO_JYUMONJIKIRI,                  sd->spamcount_KO_JYUMONJIKIRI,                  battle_config.kd_KO_JYUMONJIKIRI,                  battle_config.kdw_KO_JYUMONJIKIRI))                  { sd->spamcount_KO_JYUMONJIKIRI = sd->k_tick_c; return 0; }                  sd->spamcount_KO_JYUMONJIKIRI = 0;                  sd->spamtick_KO_JYUMONJIKIRI = tick + sd->kdelay;                  break;
			case KO_SETSUDAN:                      if (k_tick_check(sd, sd->spamtick_KO_SETSUDAN,                      sd->spamcount_KO_SETSUDAN,                      battle_config.kd_KO_SETSUDAN,                      battle_config.kdw_KO_SETSUDAN))                      { sd->spamcount_KO_SETSUDAN = sd->k_tick_c; return 0; }                      sd->spamcount_KO_SETSUDAN = 0;                      sd->spamtick_KO_SETSUDAN = tick + sd->kdelay;                      break;
			case KO_BAKURETSU:                     if (k_tick_check(sd, sd->spamtick_KO_BAKURETSU,                     sd->spamcount_KO_BAKURETSU,                     battle_config.kd_KO_BAKURETSU,                     battle_config.kdw_KO_BAKURETSU))                     { sd->spamcount_KO_BAKURETSU = sd->k_tick_c; return 0; }                     sd->spamcount_KO_BAKURETSU = 0;                     sd->spamtick_KO_BAKURETSU = tick + sd->kdelay;                     break;
			case KO_HAPPOKUNAI:                    if (k_tick_check(sd, sd->spamtick_KO_HAPPOKUNAI,                    sd->spamcount_KO_HAPPOKUNAI,                    battle_config.kd_KO_HAPPOKUNAI,                    battle_config.kdw_KO_HAPPOKUNAI))                    { sd->spamcount_KO_HAPPOKUNAI = sd->k_tick_c; return 0; }                    sd->spamcount_KO_HAPPOKUNAI = 0;                    sd->spamtick_KO_HAPPOKUNAI = tick + sd->kdelay;                    break;
			case KO_MUCHANAGE:                     if (k_tick_check(sd, sd->spamtick_KO_MUCHANAGE,                     sd->spamcount_KO_MUCHANAGE,                     battle_config.kd_KO_MUCHANAGE,                     battle_config.kdw_KO_MUCHANAGE))                     { sd->spamcount_KO_MUCHANAGE = sd->k_tick_c; return 0; }                     sd->spamcount_KO_MUCHANAGE = 0;                     sd->spamtick_KO_MUCHANAGE = tick + sd->kdelay;                     break;
			case KO_HUUMARANKA:                    if (k_tick_check(sd, sd->spamtick_KO_HUUMARANKA,                    sd->spamcount_KO_HUUMARANKA,                    battle_config.kd_KO_HUUMARANKA,                    battle_config.kdw_KO_HUUMARANKA))                    { sd->spamcount_KO_HUUMARANKA = sd->k_tick_c; return 0; }                    sd->spamcount_KO_HUUMARANKA = 0;                    sd->spamtick_KO_HUUMARANKA = tick + sd->kdelay;                    break;
			case KO_MAKIBISHI:                     if (k_tick_check(sd, sd->spamtick_KO_MAKIBISHI,                     sd->spamcount_KO_MAKIBISHI,                     battle_config.kd_KO_MAKIBISHI,                     battle_config.kdw_KO_MAKIBISHI))                     { sd->spamcount_KO_MAKIBISHI = sd->k_tick_c; return 0; }                     sd->spamcount_KO_MAKIBISHI = 0;                     sd->spamtick_KO_MAKIBISHI = tick + sd->kdelay;                     break;
			case KO_MEIKYOUSISUI:                  if (k_tick_check(sd, sd->spamtick_KO_MEIKYOUSISUI,                  sd->spamcount_KO_MEIKYOUSISUI,                  battle_config.kd_KO_MEIKYOUSISUI,                  battle_config.kdw_KO_MEIKYOUSISUI))                  { sd->spamcount_KO_MEIKYOUSISUI = sd->k_tick_c; return 0; }                  sd->spamcount_KO_MEIKYOUSISUI = 0;                  sd->spamtick_KO_MEIKYOUSISUI = tick + sd->kdelay;                  break;
			case KO_ZANZOU:                        if (k_tick_check(sd, sd->spamtick_KO_ZANZOU,                        sd->spamcount_KO_ZANZOU,                        battle_config.kd_KO_ZANZOU,                        battle_config.kdw_KO_ZANZOU))                        { sd->spamcount_KO_ZANZOU = sd->k_tick_c; return 0; }                        sd->spamcount_KO_ZANZOU = 0;                        sd->spamtick_KO_ZANZOU = tick + sd->kdelay;                        break;
			case KO_KYOUGAKU:                      if (k_tick_check(sd, sd->spamtick_KO_KYOUGAKU,                      sd->spamcount_KO_KYOUGAKU,                      battle_config.kd_KO_KYOUGAKU,                      battle_config.kdw_KO_KYOUGAKU))                      { sd->spamcount_KO_KYOUGAKU = sd->k_tick_c; return 0; }                      sd->spamcount_KO_KYOUGAKU = 0;                      sd->spamtick_KO_KYOUGAKU = tick + sd->kdelay;                      break;
			case KO_JYUSATSU:                      if (k_tick_check(sd, sd->spamtick_KO_JYUSATSU,                      sd->spamcount_KO_JYUSATSU,                      battle_config.kd_KO_JYUSATSU,                      battle_config.kdw_KO_JYUSATSU))                      { sd->spamcount_KO_JYUSATSU = sd->k_tick_c; return 0; }                      sd->spamcount_KO_JYUSATSU = 0;                      sd->spamtick_KO_JYUSATSU = tick + sd->kdelay;                      break;
			case KO_KAHU_ENTEN:                    if (k_tick_check(sd, sd->spamtick_KO_KAHU_ENTEN,                    sd->spamcount_KO_KAHU_ENTEN,                    battle_config.kd_KO_KAHU_ENTEN,                    battle_config.kdw_KO_KAHU_ENTEN))                    { sd->spamcount_KO_KAHU_ENTEN = sd->k_tick_c; return 0; }                    sd->spamcount_KO_KAHU_ENTEN = 0;                    sd->spamtick_KO_KAHU_ENTEN = tick + sd->kdelay;                    break;
			case KO_HYOUHU_HUBUKI:                 if (k_tick_check(sd, sd->spamtick_KO_HYOUHU_HUBUKI,                 sd->spamcount_KO_HYOUHU_HUBUKI,                 battle_config.kd_KO_HYOUHU_HUBUKI,                 battle_config.kdw_KO_HYOUHU_HUBUKI))                 { sd->spamcount_KO_HYOUHU_HUBUKI = sd->k_tick_c; return 0; }                 sd->spamcount_KO_HYOUHU_HUBUKI = 0;                 sd->spamtick_KO_HYOUHU_HUBUKI = tick + sd->kdelay;                 break;
			case KO_KAZEHU_SEIRAN:                 if (k_tick_check(sd, sd->spamtick_KO_KAZEHU_SEIRAN,                 sd->spamcount_KO_KAZEHU_SEIRAN,                 battle_config.kd_KO_KAZEHU_SEIRAN,                 battle_config.kdw_KO_KAZEHU_SEIRAN))                 { sd->spamcount_KO_KAZEHU_SEIRAN = sd->k_tick_c; return 0; }                 sd->spamcount_KO_KAZEHU_SEIRAN = 0;                 sd->spamtick_KO_KAZEHU_SEIRAN = tick + sd->kdelay;                 break;
			case KO_DOHU_KOUKAI:                   if (k_tick_check(sd, sd->spamtick_KO_DOHU_KOUKAI,                   sd->spamcount_KO_DOHU_KOUKAI,                   battle_config.kd_KO_DOHU_KOUKAI,                   battle_config.kdw_KO_DOHU_KOUKAI))                   { sd->spamcount_KO_DOHU_KOUKAI = sd->k_tick_c; return 0; }                   sd->spamcount_KO_DOHU_KOUKAI = 0;                   sd->spamtick_KO_DOHU_KOUKAI = tick + sd->kdelay;                   break;
			case KO_KAIHOU:                        if (k_tick_check(sd, sd->spamtick_KO_KAIHOU,                        sd->spamcount_KO_KAIHOU,                        battle_config.kd_KO_KAIHOU,                        battle_config.kdw_KO_KAIHOU))                        { sd->spamcount_KO_KAIHOU = sd->k_tick_c; return 0; }                        sd->spamcount_KO_KAIHOU = 0;                        sd->spamtick_KO_KAIHOU = tick + sd->kdelay;                        break;
			case KO_ZENKAI:                        if (k_tick_check(sd, sd->spamtick_KO_ZENKAI,                        sd->spamcount_KO_ZENKAI,                        battle_config.kd_KO_ZENKAI,                        battle_config.kdw_KO_ZENKAI))                        { sd->spamcount_KO_ZENKAI = sd->k_tick_c; return 0; }                        sd->spamcount_KO_ZENKAI = 0;                        sd->spamtick_KO_ZENKAI = tick + sd->kdelay;                        break;
			case KO_GENWAKU:                       if (k_tick_check(sd, sd->spamtick_KO_GENWAKU,                       sd->spamcount_KO_GENWAKU,                       battle_config.kd_KO_GENWAKU,                       battle_config.kdw_KO_GENWAKU))                       { sd->spamcount_KO_GENWAKU = sd->k_tick_c; return 0; }                       sd->spamcount_KO_GENWAKU = 0;                       sd->spamtick_KO_GENWAKU = tick + sd->kdelay;                       break;
			case KO_IZAYOI:                        if (k_tick_check(sd, sd->spamtick_KO_IZAYOI,                        sd->spamcount_KO_IZAYOI,                        battle_config.kd_KO_IZAYOI,                        battle_config.kdw_KO_IZAYOI))                        { sd->spamcount_KO_IZAYOI = sd->k_tick_c; return 0; }                        sd->spamcount_KO_IZAYOI = 0;                        sd->spamtick_KO_IZAYOI = tick + sd->kdelay;                        break;
			case KG_KAGEHUMI:                      if (k_tick_check(sd, sd->spamtick_KG_KAGEHUMI,                      sd->spamcount_KG_KAGEHUMI,                      battle_config.kd_KG_KAGEHUMI,                      battle_config.kdw_KG_KAGEHUMI))                      { sd->spamcount_KG_KAGEHUMI = sd->k_tick_c; return 0; }                      sd->spamcount_KG_KAGEHUMI = 0;                      sd->spamtick_KG_KAGEHUMI = tick + sd->kdelay;                      break;
			case KG_KYOMU:                         if (k_tick_check(sd, sd->spamtick_KG_KYOMU,                         sd->spamcount_KG_KYOMU,                         battle_config.kd_KG_KYOMU,                         battle_config.kdw_KG_KYOMU))                         { sd->spamcount_KG_KYOMU = sd->k_tick_c; return 0; }                         sd->spamcount_KG_KYOMU = 0;                         sd->spamtick_KG_KYOMU = tick + sd->kdelay;                         break;
			case KG_KAGEMUSYA:                     if (k_tick_check(sd, sd->spamtick_KG_KAGEMUSYA,                     sd->spamcount_KG_KAGEMUSYA,                     battle_config.kd_KG_KAGEMUSYA,                     battle_config.kdw_KG_KAGEMUSYA))                     { sd->spamcount_KG_KAGEMUSYA = sd->k_tick_c; return 0; }                     sd->spamcount_KG_KAGEMUSYA = 0;                     sd->spamtick_KG_KAGEMUSYA = tick + sd->kdelay;                     break;
			case OB_ZANGETSU:                      if (k_tick_check(sd, sd->spamtick_OB_ZANGETSU,                      sd->spamcount_OB_ZANGETSU,                      battle_config.kd_OB_ZANGETSU,                      battle_config.kdw_OB_ZANGETSU))                      { sd->spamcount_OB_ZANGETSU = sd->k_tick_c; return 0; }                      sd->spamcount_OB_ZANGETSU = 0;                      sd->spamtick_OB_ZANGETSU = tick + sd->kdelay;                      break;
			case OB_OBOROGENSOU:                   if (k_tick_check(sd, sd->spamtick_OB_OBOROGENSOU,                   sd->spamcount_OB_OBOROGENSOU,                   battle_config.kd_OB_OBOROGENSOU,                   battle_config.kdw_OB_OBOROGENSOU))                   { sd->spamcount_OB_OBOROGENSOU = sd->k_tick_c; return 0; }                   sd->spamcount_OB_OBOROGENSOU = 0;                   sd->spamtick_OB_OBOROGENSOU = tick + sd->kdelay;                   break;
			case OB_AKAITSUKI:                     if (k_tick_check(sd, sd->spamtick_OB_AKAITSUKI,                     sd->spamcount_OB_AKAITSUKI,                     battle_config.kd_OB_AKAITSUKI,                     battle_config.kdw_OB_AKAITSUKI))                     { sd->spamcount_OB_AKAITSUKI = sd->k_tick_c; return 0; }                     sd->spamcount_OB_AKAITSUKI = 0;                     sd->spamtick_OB_AKAITSUKI = tick + sd->kdelay;                     break;
			case GC_DARKCROW:                      if (k_tick_check(sd, sd->spamtick_GC_DARKCROW,                      sd->spamcount_GC_DARKCROW,                      battle_config.kd_GC_DARKCROW,                      battle_config.kdw_GC_DARKCROW))                      { sd->spamcount_GC_DARKCROW = sd->k_tick_c; return 0; }                      sd->spamcount_GC_DARKCROW = 0;                      sd->spamtick_GC_DARKCROW = tick + sd->kdelay;                      break;
			case RA_UNLIMIT:                       if (k_tick_check(sd, sd->spamtick_RA_UNLIMIT,                       sd->spamcount_RA_UNLIMIT,                       battle_config.kd_RA_UNLIMIT,                       battle_config.kdw_RA_UNLIMIT))                       { sd->spamcount_RA_UNLIMIT = sd->k_tick_c; return 0; }                       sd->spamcount_RA_UNLIMIT = 0;                       sd->spamtick_RA_UNLIMIT = tick + sd->kdelay;                       break;
			case GN_ILLUSIONDOPING:                if (k_tick_check(sd, sd->spamtick_GN_ILLUSIONDOPING,                sd->spamcount_GN_ILLUSIONDOPING,                battle_config.kd_GN_ILLUSIONDOPING,                battle_config.kdw_GN_ILLUSIONDOPING))                { sd->spamcount_GN_ILLUSIONDOPING = sd->k_tick_c; return 0; }                sd->spamcount_GN_ILLUSIONDOPING = 0;                sd->spamtick_GN_ILLUSIONDOPING = tick + sd->kdelay;                break;
			case RK_DRAGONBREATH_WATER:            if (k_tick_check(sd, sd->spamtick_RK_DRAGONBREATH_WATER,            sd->spamcount_RK_DRAGONBREATH_WATER,            battle_config.kd_RK_DRAGONBREATH_WATER,            battle_config.kdw_RK_DRAGONBREATH_WATER))            { sd->spamcount_RK_DRAGONBREATH_WATER = sd->k_tick_c; return 0; }            sd->spamcount_RK_DRAGONBREATH_WATER = 0;            sd->spamtick_RK_DRAGONBREATH_WATER = tick + sd->kdelay;            break;
			case RK_LUXANIMA:                      if (k_tick_check(sd, sd->spamtick_RK_LUXANIMA,                      sd->spamcount_RK_LUXANIMA,                      battle_config.kd_RK_LUXANIMA,                      battle_config.kdw_RK_LUXANIMA))                      { sd->spamcount_RK_LUXANIMA = sd->k_tick_c; return 0; }                      sd->spamcount_RK_LUXANIMA = 0;                      sd->spamtick_RK_LUXANIMA = tick + sd->kdelay;                      break;
			case NC_MAGMA_ERUPTION:                if (k_tick_check(sd, sd->spamtick_NC_MAGMA_ERUPTION,                sd->spamcount_NC_MAGMA_ERUPTION,                battle_config.kd_NC_MAGMA_ERUPTION,                battle_config.kdw_NC_MAGMA_ERUPTION))                { sd->spamcount_NC_MAGMA_ERUPTION = sd->k_tick_c; return 0; }                sd->spamcount_NC_MAGMA_ERUPTION = 0;                sd->spamtick_NC_MAGMA_ERUPTION = tick + sd->kdelay;                break;
			case WM_FRIGG_SONG:                    if (k_tick_check(sd, sd->spamtick_WM_FRIGG_SONG,                    sd->spamcount_WM_FRIGG_SONG,                    battle_config.kd_WM_FRIGG_SONG,                    battle_config.kdw_WM_FRIGG_SONG))                    { sd->spamcount_WM_FRIGG_SONG = sd->k_tick_c; return 0; }                    sd->spamcount_WM_FRIGG_SONG = 0;                    sd->spamtick_WM_FRIGG_SONG = tick + sd->kdelay;                    break;
			case SO_ELEMENTAL_SHIELD:              if (k_tick_check(sd, sd->spamtick_SO_ELEMENTAL_SHIELD,              sd->spamcount_SO_ELEMENTAL_SHIELD,              battle_config.kd_SO_ELEMENTAL_SHIELD,              battle_config.kdw_SO_ELEMENTAL_SHIELD))              { sd->spamcount_SO_ELEMENTAL_SHIELD = sd->k_tick_c; return 0; }              sd->spamcount_SO_ELEMENTAL_SHIELD = 0;              sd->spamtick_SO_ELEMENTAL_SHIELD = tick + sd->kdelay;              break;
			case SR_FLASHCOMBO:                    if (k_tick_check(sd, sd->spamtick_SR_FLASHCOMBO,                    sd->spamcount_SR_FLASHCOMBO,                    battle_config.kd_SR_FLASHCOMBO,                    battle_config.kdw_SR_FLASHCOMBO))                    { sd->spamcount_SR_FLASHCOMBO = sd->k_tick_c; return 0; }                    sd->spamcount_SR_FLASHCOMBO = 0;                    sd->spamtick_SR_FLASHCOMBO = tick + sd->kdelay;                    break;
			case SC_ESCAPE:                        if (k_tick_check(sd, sd->spamtick_SC_ESCAPE,                        sd->spamcount_SC_ESCAPE,                        battle_config.kd_SC_ESCAPE,                        battle_config.kdw_SC_ESCAPE))                        { sd->spamcount_SC_ESCAPE = sd->k_tick_c; return 0; }                        sd->spamcount_SC_ESCAPE = 0;                        sd->spamtick_SC_ESCAPE = tick + sd->kdelay;                        break;
			case AB_OFFERTORIUM:                   if (k_tick_check(sd, sd->spamtick_AB_OFFERTORIUM,                   sd->spamcount_AB_OFFERTORIUM,                   battle_config.kd_AB_OFFERTORIUM,                   battle_config.kdw_AB_OFFERTORIUM))                   { sd->spamcount_AB_OFFERTORIUM = sd->k_tick_c; return 0; }                   sd->spamcount_AB_OFFERTORIUM = 0;                   sd->spamtick_AB_OFFERTORIUM = tick + sd->kdelay;                   break;
			case WL_TELEKINESIS_INTENSE:           if (k_tick_check(sd, sd->spamtick_WL_TELEKINESIS_INTENSE,           sd->spamcount_WL_TELEKINESIS_INTENSE,           battle_config.kd_WL_TELEKINESIS_INTENSE,           battle_config.kdw_WL_TELEKINESIS_INTENSE))           { sd->spamcount_WL_TELEKINESIS_INTENSE = sd->k_tick_c; return 0; }           sd->spamcount_WL_TELEKINESIS_INTENSE = 0;           sd->spamtick_WL_TELEKINESIS_INTENSE = tick + sd->kdelay;           break;
			case ALL_FULL_THROTTLE:                if (k_tick_check(sd, sd->spamtick_ALL_FULL_THROTTLE,                sd->spamcount_ALL_FULL_THROTTLE,                battle_config.kd_ALL_FULL_THROTTLE,                battle_config.kdw_ALL_FULL_THROTTLE))                { sd->spamcount_ALL_FULL_THROTTLE = sd->k_tick_c; return 0; }                sd->spamcount_ALL_FULL_THROTTLE = 0;                sd->spamtick_ALL_FULL_THROTTLE = tick + sd->kdelay;                break;
			case SU_BITE:                          if (k_tick_check(sd, sd->spamtick_SU_BITE,                          sd->spamcount_SU_BITE,                          battle_config.kd_SU_BITE,                          battle_config.kdw_SU_BITE))                          { sd->spamcount_SU_BITE = sd->k_tick_c; return 0; }                          sd->spamcount_SU_BITE = 0;                          sd->spamtick_SU_BITE = tick + sd->kdelay;                          break;
			case SU_SCRATCH:                       if (k_tick_check(sd, sd->spamtick_SU_SCRATCH,                       sd->spamcount_SU_SCRATCH,                       battle_config.kd_SU_SCRATCH,                       battle_config.kdw_SU_SCRATCH))                       { sd->spamcount_SU_SCRATCH = sd->k_tick_c; return 0; }                       sd->spamcount_SU_SCRATCH = 0;                       sd->spamtick_SU_SCRATCH = tick + sd->kdelay;                       break;
			case SU_STOOP:                         if (k_tick_check(sd, sd->spamtick_SU_STOOP,                         sd->spamcount_SU_STOOP,                         battle_config.kd_SU_STOOP,                         battle_config.kdw_SU_STOOP))                         { sd->spamcount_SU_STOOP = sd->k_tick_c; return 0; }                         sd->spamcount_SU_STOOP = 0;                         sd->spamtick_SU_STOOP = tick + sd->kdelay;                         break;
			case SU_LOPE:                          if (k_tick_check(sd, sd->spamtick_SU_LOPE,                          sd->spamcount_SU_LOPE,                          battle_config.kd_SU_LOPE,                          battle_config.kdw_SU_LOPE))                          { sd->spamcount_SU_LOPE = sd->k_tick_c; return 0; }                          sd->spamcount_SU_LOPE = 0;                          sd->spamtick_SU_LOPE = tick + sd->kdelay;                          break;
			case SU_SPRITEMABLE:                   if (k_tick_check(sd, sd->spamtick_SU_SPRITEMABLE,                   sd->spamcount_SU_SPRITEMABLE,                   battle_config.kd_SU_SPRITEMABLE,                   battle_config.kdw_SU_SPRITEMABLE))                   { sd->spamcount_SU_SPRITEMABLE = sd->k_tick_c; return 0; }                   sd->spamcount_SU_SPRITEMABLE = 0;                   sd->spamtick_SU_SPRITEMABLE = tick + sd->kdelay;                   break;
			case SU_POWEROFLAND:                   if (k_tick_check(sd, sd->spamtick_SU_POWEROFLAND,                   sd->spamcount_SU_POWEROFLAND,                   battle_config.kd_SU_POWEROFLAND,                   battle_config.kdw_SU_POWEROFLAND))                   { sd->spamcount_SU_POWEROFLAND = sd->k_tick_c; return 0; }                   sd->spamcount_SU_POWEROFLAND = 0;                   sd->spamtick_SU_POWEROFLAND = tick + sd->kdelay;                   break;
			case SU_SV_STEMSPEAR:                  if (k_tick_check(sd, sd->spamtick_SU_SV_STEMSPEAR,                  sd->spamcount_SU_SV_STEMSPEAR,                  battle_config.kd_SU_SV_STEMSPEAR,                  battle_config.kdw_SU_SV_STEMSPEAR))                  { sd->spamcount_SU_SV_STEMSPEAR = sd->k_tick_c; return 0; }                  sd->spamcount_SU_SV_STEMSPEAR = 0;                  sd->spamtick_SU_SV_STEMSPEAR = tick + sd->kdelay;                  break;
			case SU_CN_POWDERING:                  if (k_tick_check(sd, sd->spamtick_SU_CN_POWDERING,                  sd->spamcount_SU_CN_POWDERING,                  battle_config.kd_SU_CN_POWDERING,                  battle_config.kdw_SU_CN_POWDERING))                  { sd->spamcount_SU_CN_POWDERING = sd->k_tick_c; return 0; }                  sd->spamcount_SU_CN_POWDERING = 0;                  sd->spamtick_SU_CN_POWDERING = tick + sd->kdelay;                  break;
			case SU_CN_METEOR:                     if (k_tick_check(sd, sd->spamtick_SU_CN_METEOR,                     sd->spamcount_SU_CN_METEOR,                     battle_config.kd_SU_CN_METEOR,                     battle_config.kdw_SU_CN_METEOR))                     { sd->spamcount_SU_CN_METEOR = sd->k_tick_c; return 0; }                     sd->spamcount_SU_CN_METEOR = 0;                     sd->spamtick_SU_CN_METEOR = tick + sd->kdelay;                     break;
			case SU_SV_ROOTTWIST:                  if (k_tick_check(sd, sd->spamtick_SU_SV_ROOTTWIST,                  sd->spamcount_SU_SV_ROOTTWIST,                  battle_config.kd_SU_SV_ROOTTWIST,                  battle_config.kdw_SU_SV_ROOTTWIST))                  { sd->spamcount_SU_SV_ROOTTWIST = sd->k_tick_c; return 0; }                  sd->spamcount_SU_SV_ROOTTWIST = 0;                  sd->spamtick_SU_SV_ROOTTWIST = tick + sd->kdelay;                  break;
			case SU_POWEROFLIFE:                   if (k_tick_check(sd, sd->spamtick_SU_POWEROFLIFE,                   sd->spamcount_SU_POWEROFLIFE,                   battle_config.kd_SU_POWEROFLIFE,                   battle_config.kdw_SU_POWEROFLIFE))                   { sd->spamcount_SU_POWEROFLIFE = sd->k_tick_c; return 0; }                   sd->spamcount_SU_POWEROFLIFE = 0;                   sd->spamtick_SU_POWEROFLIFE = tick + sd->kdelay;                   break;
			case SU_SCAROFTAROU:                   if (k_tick_check(sd, sd->spamtick_SU_SCAROFTAROU,                   sd->spamcount_SU_SCAROFTAROU,                   battle_config.kd_SU_SCAROFTAROU,                   battle_config.kdw_SU_SCAROFTAROU))                   { sd->spamcount_SU_SCAROFTAROU = sd->k_tick_c; return 0; }                   sd->spamcount_SU_SCAROFTAROU = 0;                   sd->spamtick_SU_SCAROFTAROU = tick + sd->kdelay;                   break;
			case SU_PICKYPECK:                     if (k_tick_check(sd, sd->spamtick_SU_PICKYPECK,                     sd->spamcount_SU_PICKYPECK,                     battle_config.kd_SU_PICKYPECK,                     battle_config.kdw_SU_PICKYPECK))                     { sd->spamcount_SU_PICKYPECK = sd->k_tick_c; return 0; }                     sd->spamcount_SU_PICKYPECK = 0;                     sd->spamtick_SU_PICKYPECK = tick + sd->kdelay;                     break;
			case SU_ARCLOUSEDASH:                  if (k_tick_check(sd, sd->spamtick_SU_ARCLOUSEDASH,                  sd->spamcount_SU_ARCLOUSEDASH,                  battle_config.kd_SU_ARCLOUSEDASH,                  battle_config.kdw_SU_ARCLOUSEDASH))                  { sd->spamcount_SU_ARCLOUSEDASH = sd->k_tick_c; return 0; }                  sd->spamcount_SU_ARCLOUSEDASH = 0;                  sd->spamtick_SU_ARCLOUSEDASH = tick + sd->kdelay;                  break;
			case SU_LUNATICCARROTBEAT:             if (k_tick_check(sd, sd->spamtick_SU_LUNATICCARROTBEAT,             sd->spamcount_SU_LUNATICCARROTBEAT,             battle_config.kd_SU_LUNATICCARROTBEAT,             battle_config.kdw_SU_LUNATICCARROTBEAT))             { sd->spamcount_SU_LUNATICCARROTBEAT = sd->k_tick_c; return 0; }             sd->spamcount_SU_LUNATICCARROTBEAT = 0;             sd->spamtick_SU_LUNATICCARROTBEAT = tick + sd->kdelay;             break;
			case SU_POWEROFSEA:                    if (k_tick_check(sd, sd->spamtick_SU_POWEROFSEA,                    sd->spamcount_SU_POWEROFSEA,                    battle_config.kd_SU_POWEROFSEA,                    battle_config.kdw_SU_POWEROFSEA))                    { sd->spamcount_SU_POWEROFSEA = sd->k_tick_c; return 0; }                    sd->spamcount_SU_POWEROFSEA = 0;                    sd->spamtick_SU_POWEROFSEA = tick + sd->kdelay;                    break;
			case SU_TUNABELLY:                     if (k_tick_check(sd, sd->spamtick_SU_TUNABELLY,                     sd->spamcount_SU_TUNABELLY,                     battle_config.kd_SU_TUNABELLY,                     battle_config.kdw_SU_TUNABELLY))                     { sd->spamcount_SU_TUNABELLY = sd->k_tick_c; return 0; }                     sd->spamcount_SU_TUNABELLY = 0;                     sd->spamtick_SU_TUNABELLY = tick + sd->kdelay;                     break;
			case SU_TUNAPARTY:                     if (k_tick_check(sd, sd->spamtick_SU_TUNAPARTY,                     sd->spamcount_SU_TUNAPARTY,                     battle_config.kd_SU_TUNAPARTY,                     battle_config.kdw_SU_TUNAPARTY))                     { sd->spamcount_SU_TUNAPARTY = sd->k_tick_c; return 0; }                     sd->spamcount_SU_TUNAPARTY = 0;                     sd->spamtick_SU_TUNAPARTY = tick + sd->kdelay;                     break;
			case SU_BUNCHOFSHRIMP:                 if (k_tick_check(sd, sd->spamtick_SU_BUNCHOFSHRIMP,                 sd->spamcount_SU_BUNCHOFSHRIMP,                 battle_config.kd_SU_BUNCHOFSHRIMP,                 battle_config.kdw_SU_BUNCHOFSHRIMP))                 { sd->spamcount_SU_BUNCHOFSHRIMP = sd->k_tick_c; return 0; }                 sd->spamcount_SU_BUNCHOFSHRIMP = 0;                 sd->spamtick_SU_BUNCHOFSHRIMP = tick + sd->kdelay;                 break;
			case SU_FRESHSHRIMP:                   if (k_tick_check(sd, sd->spamtick_SU_FRESHSHRIMP,                   sd->spamcount_SU_FRESHSHRIMP,                   battle_config.kd_SU_FRESHSHRIMP,                   battle_config.kdw_SU_FRESHSHRIMP))                   { sd->spamcount_SU_FRESHSHRIMP = sd->k_tick_c; return 0; }                   sd->spamcount_SU_FRESHSHRIMP = 0;                   sd->spamtick_SU_FRESHSHRIMP = tick + sd->kdelay;                   break;
			case SU_CN_METEOR2:                    if (k_tick_check(sd, sd->spamtick_SU_CN_METEOR2,                    sd->spamcount_SU_CN_METEOR2,                    battle_config.kd_SU_CN_METEOR2,                    battle_config.kdw_SU_CN_METEOR2))                    { sd->spamcount_SU_CN_METEOR2 = sd->k_tick_c; return 0; }                    sd->spamcount_SU_CN_METEOR2 = 0;                    sd->spamtick_SU_CN_METEOR2 = tick + sd->kdelay;                    break;
			case SU_LUNATICCARROTBEAT2:            if (k_tick_check(sd, sd->spamtick_SU_LUNATICCARROTBEAT2,            sd->spamcount_SU_LUNATICCARROTBEAT2,            battle_config.kd_SU_LUNATICCARROTBEAT2,            battle_config.kdw_SU_LUNATICCARROTBEAT2))            { sd->spamcount_SU_LUNATICCARROTBEAT2 = sd->k_tick_c; return 0; }            sd->spamcount_SU_LUNATICCARROTBEAT2 = 0;            sd->spamtick_SU_LUNATICCARROTBEAT2 = tick + sd->kdelay;            break;
			case SU_SOULATTACK:                    if (k_tick_check(sd, sd->spamtick_SU_SOULATTACK,                    sd->spamcount_SU_SOULATTACK,                    battle_config.kd_SU_SOULATTACK,                    battle_config.kdw_SU_SOULATTACK))                    { sd->spamcount_SU_SOULATTACK = sd->k_tick_c; return 0; }                    sd->spamcount_SU_SOULATTACK = 0;                    sd->spamtick_SU_SOULATTACK = tick + sd->kdelay;                    break;
			case SU_POWEROFFLOCK:                  if (k_tick_check(sd, sd->spamtick_SU_POWEROFFLOCK,                  sd->spamcount_SU_POWEROFFLOCK,                  battle_config.kd_SU_POWEROFFLOCK,                  battle_config.kdw_SU_POWEROFFLOCK))                  { sd->spamcount_SU_POWEROFFLOCK = sd->k_tick_c; return 0; }                  sd->spamcount_SU_POWEROFFLOCK = 0;                  sd->spamtick_SU_POWEROFFLOCK = tick + sd->kdelay;                  break;
			case SU_SVG_SPIRIT:                    if (k_tick_check(sd, sd->spamtick_SU_SVG_SPIRIT,                    sd->spamcount_SU_SVG_SPIRIT,                    battle_config.kd_SU_SVG_SPIRIT,                    battle_config.kdw_SU_SVG_SPIRIT))                    { sd->spamcount_SU_SVG_SPIRIT = sd->k_tick_c; return 0; }                    sd->spamcount_SU_SVG_SPIRIT = 0;                    sd->spamtick_SU_SVG_SPIRIT = tick + sd->kdelay;                    break;
			case SU_HISS:                          if (k_tick_check(sd, sd->spamtick_SU_HISS,                          sd->spamcount_SU_HISS,                          battle_config.kd_SU_HISS,                          battle_config.kdw_SU_HISS))                          { sd->spamcount_SU_HISS = sd->k_tick_c; return 0; }                          sd->spamcount_SU_HISS = 0;                          sd->spamtick_SU_HISS = tick + sd->kdelay;                          break;
			case SU_NYANGGRASS:                    if (k_tick_check(sd, sd->spamtick_SU_NYANGGRASS,                    sd->spamcount_SU_NYANGGRASS,                    battle_config.kd_SU_NYANGGRASS,                    battle_config.kdw_SU_NYANGGRASS))                    { sd->spamcount_SU_NYANGGRASS = sd->k_tick_c; return 0; }                    sd->spamcount_SU_NYANGGRASS = 0;                    sd->spamtick_SU_NYANGGRASS = tick + sd->kdelay;                    break;
			case SU_GROOMING:                      if (k_tick_check(sd, sd->spamtick_SU_GROOMING,                      sd->spamcount_SU_GROOMING,                      battle_config.kd_SU_GROOMING,                      battle_config.kdw_SU_GROOMING))                      { sd->spamcount_SU_GROOMING = sd->k_tick_c; return 0; }                      sd->spamcount_SU_GROOMING = 0;                      sd->spamtick_SU_GROOMING = tick + sd->kdelay;                      break;
			case SU_PURRING:                       if (k_tick_check(sd, sd->spamtick_SU_PURRING,                       sd->spamcount_SU_PURRING,                       battle_config.kd_SU_PURRING,                       battle_config.kdw_SU_PURRING))                       { sd->spamcount_SU_PURRING = sd->k_tick_c; return 0; }                       sd->spamcount_SU_PURRING = 0;                       sd->spamtick_SU_PURRING = tick + sd->kdelay;                       break;
			case SU_SHRIMPARTY:                    if (k_tick_check(sd, sd->spamtick_SU_SHRIMPARTY,                    sd->spamcount_SU_SHRIMPARTY,                    battle_config.kd_SU_SHRIMPARTY,                    battle_config.kdw_SU_SHRIMPARTY))                    { sd->spamcount_SU_SHRIMPARTY = sd->k_tick_c; return 0; }                    sd->spamcount_SU_SHRIMPARTY = 0;                    sd->spamtick_SU_SHRIMPARTY = tick + sd->kdelay;                    break;
			case SU_SPIRITOFLIFE:                  if (k_tick_check(sd, sd->spamtick_SU_SPIRITOFLIFE,                  sd->spamcount_SU_SPIRITOFLIFE,                  battle_config.kd_SU_SPIRITOFLIFE,                  battle_config.kdw_SU_SPIRITOFLIFE))                  { sd->spamcount_SU_SPIRITOFLIFE = sd->k_tick_c; return 0; }                  sd->spamcount_SU_SPIRITOFLIFE = 0;                  sd->spamtick_SU_SPIRITOFLIFE = tick + sd->kdelay;                  break;
			case SU_MEOWMEOW:                      if (k_tick_check(sd, sd->spamtick_SU_MEOWMEOW,                      sd->spamcount_SU_MEOWMEOW,                      battle_config.kd_SU_MEOWMEOW,                      battle_config.kdw_SU_MEOWMEOW))                      { sd->spamcount_SU_MEOWMEOW = sd->k_tick_c; return 0; }                      sd->spamcount_SU_MEOWMEOW = 0;                      sd->spamtick_SU_MEOWMEOW = tick + sd->kdelay;                      break;
			case SU_SPIRITOFLAND:                  if (k_tick_check(sd, sd->spamtick_SU_SPIRITOFLAND,                  sd->spamcount_SU_SPIRITOFLAND,                  battle_config.kd_SU_SPIRITOFLAND,                  battle_config.kdw_SU_SPIRITOFLAND))                  { sd->spamcount_SU_SPIRITOFLAND = sd->k_tick_c; return 0; }                  sd->spamcount_SU_SPIRITOFLAND = 0;                  sd->spamtick_SU_SPIRITOFLAND = tick + sd->kdelay;                  break;
			case SU_CHATTERING:                    if (k_tick_check(sd, sd->spamtick_SU_CHATTERING,                    sd->spamcount_SU_CHATTERING,                    battle_config.kd_SU_CHATTERING,                    battle_config.kdw_SU_CHATTERING))                    { sd->spamcount_SU_CHATTERING = sd->k_tick_c; return 0; }                    sd->spamcount_SU_CHATTERING = 0;                    sd->spamtick_SU_CHATTERING = tick + sd->kdelay;                    break;
			case SU_SPIRITOFSEA:                   if (k_tick_check(sd, sd->spamtick_SU_SPIRITOFSEA,                   sd->spamcount_SU_SPIRITOFSEA,                   battle_config.kd_SU_SPIRITOFSEA,                   battle_config.kdw_SU_SPIRITOFSEA))                   { sd->spamcount_SU_SPIRITOFSEA = sd->k_tick_c; return 0; }                   sd->spamcount_SU_SPIRITOFSEA = 0;                   sd->spamtick_SU_SPIRITOFSEA = tick + sd->kdelay;                   break;
			case CG_SPECIALSINGER:                 if (k_tick_check(sd, sd->spamtick_CG_SPECIALSINGER,                 sd->spamcount_CG_SPECIALSINGER,                 battle_config.kd_CG_SPECIALSINGER,                 battle_config.kdw_CG_SPECIALSINGER))                 { sd->spamcount_CG_SPECIALSINGER = sd->k_tick_c; return 0; }                 sd->spamcount_CG_SPECIALSINGER = 0;                 sd->spamtick_CG_SPECIALSINGER = tick + sd->kdelay;                 break;
			case AB_VITUPERATUM:                   if (k_tick_check(sd, sd->spamtick_AB_VITUPERATUM,                   sd->spamcount_AB_VITUPERATUM,                   battle_config.kd_AB_VITUPERATUM,                   battle_config.kdw_AB_VITUPERATUM))                   { sd->spamcount_AB_VITUPERATUM = sd->k_tick_c; return 0; }                   sd->spamcount_AB_VITUPERATUM = 0;                   sd->spamtick_AB_VITUPERATUM = tick + sd->kdelay;                   break;
			case AB_CONVENIO:                      if (k_tick_check(sd, sd->spamtick_AB_CONVENIO,                      sd->spamcount_AB_CONVENIO,                      battle_config.kd_AB_CONVENIO,                      battle_config.kdw_AB_CONVENIO))                      { sd->spamcount_AB_CONVENIO = sd->k_tick_c; return 0; }                      sd->spamcount_AB_CONVENIO = 0;                      sd->spamtick_AB_CONVENIO = tick + sd->kdelay;                      break;
			case DK_SERVANTWEAPON:                 if (k_tick_check(sd, sd->spamtick_DK_SERVANTWEAPON,                 sd->spamcount_DK_SERVANTWEAPON,                 battle_config.kd_DK_SERVANTWEAPON,                 battle_config.kdw_DK_SERVANTWEAPON))                 { sd->spamcount_DK_SERVANTWEAPON = sd->k_tick_c; return 0; }                 sd->spamcount_DK_SERVANTWEAPON = 0;                 sd->spamtick_DK_SERVANTWEAPON = tick + sd->kdelay;                 break;
			case DK_SERVANT_W_SIGN:                if (k_tick_check(sd, sd->spamtick_DK_SERVANT_W_SIGN,                sd->spamcount_DK_SERVANT_W_SIGN,                battle_config.kd_DK_SERVANT_W_SIGN,                battle_config.kdw_DK_SERVANT_W_SIGN))                { sd->spamcount_DK_SERVANT_W_SIGN = sd->k_tick_c; return 0; }                sd->spamcount_DK_SERVANT_W_SIGN = 0;                sd->spamtick_DK_SERVANT_W_SIGN = tick + sd->kdelay;                break;
			case DK_SERVANT_W_PHANTOM:             if (k_tick_check(sd, sd->spamtick_DK_SERVANT_W_PHANTOM,             sd->spamcount_DK_SERVANT_W_PHANTOM,             battle_config.kd_DK_SERVANT_W_PHANTOM,             battle_config.kdw_DK_SERVANT_W_PHANTOM))             { sd->spamcount_DK_SERVANT_W_PHANTOM = sd->k_tick_c; return 0; }             sd->spamcount_DK_SERVANT_W_PHANTOM = 0;             sd->spamtick_DK_SERVANT_W_PHANTOM = tick + sd->kdelay;             break;
			case DK_SERVANT_W_DEMOL:               if (k_tick_check(sd, sd->spamtick_DK_SERVANT_W_DEMOL,               sd->spamcount_DK_SERVANT_W_DEMOL,               battle_config.kd_DK_SERVANT_W_DEMOL,               battle_config.kdw_DK_SERVANT_W_DEMOL))               { sd->spamcount_DK_SERVANT_W_DEMOL = sd->k_tick_c; return 0; }               sd->spamcount_DK_SERVANT_W_DEMOL = 0;               sd->spamtick_DK_SERVANT_W_DEMOL = tick + sd->kdelay;               break;
			case DK_CHARGINGPIERCE:                if (k_tick_check(sd, sd->spamtick_DK_CHARGINGPIERCE,                sd->spamcount_DK_CHARGINGPIERCE,                battle_config.kd_DK_CHARGINGPIERCE,                battle_config.kdw_DK_CHARGINGPIERCE))                { sd->spamcount_DK_CHARGINGPIERCE = sd->k_tick_c; return 0; }                sd->spamcount_DK_CHARGINGPIERCE = 0;                sd->spamtick_DK_CHARGINGPIERCE = tick + sd->kdelay;                break;
			case DK_HACKANDSLASHER:                if (k_tick_check(sd, sd->spamtick_DK_HACKANDSLASHER,                sd->spamcount_DK_HACKANDSLASHER,                battle_config.kd_DK_HACKANDSLASHER,                battle_config.kdw_DK_HACKANDSLASHER))                { sd->spamcount_DK_HACKANDSLASHER = sd->k_tick_c; return 0; }                sd->spamcount_DK_HACKANDSLASHER = 0;                sd->spamtick_DK_HACKANDSLASHER = tick + sd->kdelay;                break;
			case DK_DRAGONIC_AURA:                 if (k_tick_check(sd, sd->spamtick_DK_DRAGONIC_AURA,                 sd->spamcount_DK_DRAGONIC_AURA,                 battle_config.kd_DK_DRAGONIC_AURA,                 battle_config.kdw_DK_DRAGONIC_AURA))                 { sd->spamcount_DK_DRAGONIC_AURA = sd->k_tick_c; return 0; }                 sd->spamcount_DK_DRAGONIC_AURA = 0;                 sd->spamtick_DK_DRAGONIC_AURA = tick + sd->kdelay;                 break;
			case DK_MADNESS_CRUSHER:               if (k_tick_check(sd, sd->spamtick_DK_MADNESS_CRUSHER,               sd->spamcount_DK_MADNESS_CRUSHER,               battle_config.kd_DK_MADNESS_CRUSHER,               battle_config.kdw_DK_MADNESS_CRUSHER))               { sd->spamcount_DK_MADNESS_CRUSHER = sd->k_tick_c; return 0; }               sd->spamcount_DK_MADNESS_CRUSHER = 0;               sd->spamtick_DK_MADNESS_CRUSHER = tick + sd->kdelay;               break;
			case DK_VIGOR:                         if (k_tick_check(sd, sd->spamtick_DK_VIGOR,                         sd->spamcount_DK_VIGOR,                         battle_config.kd_DK_VIGOR,                         battle_config.kdw_DK_VIGOR))                         { sd->spamcount_DK_VIGOR = sd->k_tick_c; return 0; }                         sd->spamcount_DK_VIGOR = 0;                         sd->spamtick_DK_VIGOR = tick + sd->kdelay;                         break;
			case DK_STORMSLASH:                    if (k_tick_check(sd, sd->spamtick_DK_STORMSLASH,                    sd->spamcount_DK_STORMSLASH,                    battle_config.kd_DK_STORMSLASH,                    battle_config.kdw_DK_STORMSLASH))                    { sd->spamcount_DK_STORMSLASH = sd->k_tick_c; return 0; }                    sd->spamcount_DK_STORMSLASH = 0;                    sd->spamtick_DK_STORMSLASH = tick + sd->kdelay;                    break;
			case AG_DEADLY_PROJECTION:             if (k_tick_check(sd, sd->spamtick_AG_DEADLY_PROJECTION,             sd->spamcount_AG_DEADLY_PROJECTION,             battle_config.kd_AG_DEADLY_PROJECTION,             battle_config.kdw_AG_DEADLY_PROJECTION))             { sd->spamcount_AG_DEADLY_PROJECTION = sd->k_tick_c; return 0; }             sd->spamcount_AG_DEADLY_PROJECTION = 0;             sd->spamtick_AG_DEADLY_PROJECTION = tick + sd->kdelay;             break;
			case AG_DESTRUCTIVE_HURRICANE:         if (k_tick_check(sd, sd->spamtick_AG_DESTRUCTIVE_HURRICANE,         sd->spamcount_AG_DESTRUCTIVE_HURRICANE,         battle_config.kd_AG_DESTRUCTIVE_HURRICANE,         battle_config.kdw_AG_DESTRUCTIVE_HURRICANE))         { sd->spamcount_AG_DESTRUCTIVE_HURRICANE = sd->k_tick_c; return 0; }         sd->spamcount_AG_DESTRUCTIVE_HURRICANE = 0;         sd->spamtick_AG_DESTRUCTIVE_HURRICANE = tick + sd->kdelay;         break;
			case AG_RAIN_OF_CRYSTAL:               if (k_tick_check(sd, sd->spamtick_AG_RAIN_OF_CRYSTAL,               sd->spamcount_AG_RAIN_OF_CRYSTAL,               battle_config.kd_AG_RAIN_OF_CRYSTAL,               battle_config.kdw_AG_RAIN_OF_CRYSTAL))               { sd->spamcount_AG_RAIN_OF_CRYSTAL = sd->k_tick_c; return 0; }               sd->spamcount_AG_RAIN_OF_CRYSTAL = 0;               sd->spamtick_AG_RAIN_OF_CRYSTAL = tick + sd->kdelay;               break;
			case AG_MYSTERY_ILLUSION:              if (k_tick_check(sd, sd->spamtick_AG_MYSTERY_ILLUSION,              sd->spamcount_AG_MYSTERY_ILLUSION,              battle_config.kd_AG_MYSTERY_ILLUSION,              battle_config.kdw_AG_MYSTERY_ILLUSION))              { sd->spamcount_AG_MYSTERY_ILLUSION = sd->k_tick_c; return 0; }              sd->spamcount_AG_MYSTERY_ILLUSION = 0;              sd->spamtick_AG_MYSTERY_ILLUSION = tick + sd->kdelay;              break;
			case AG_VIOLENT_QUAKE:                 if (k_tick_check(sd, sd->spamtick_AG_VIOLENT_QUAKE,                 sd->spamcount_AG_VIOLENT_QUAKE,                 battle_config.kd_AG_VIOLENT_QUAKE,                 battle_config.kdw_AG_VIOLENT_QUAKE))                 { sd->spamcount_AG_VIOLENT_QUAKE = sd->k_tick_c; return 0; }                 sd->spamcount_AG_VIOLENT_QUAKE = 0;                 sd->spamtick_AG_VIOLENT_QUAKE = tick + sd->kdelay;                 break;
			case AG_SOUL_VC_STRIKE:                if (k_tick_check(sd, sd->spamtick_AG_SOUL_VC_STRIKE,                sd->spamcount_AG_SOUL_VC_STRIKE,                battle_config.kd_AG_SOUL_VC_STRIKE,                battle_config.kdw_AG_SOUL_VC_STRIKE))                { sd->spamcount_AG_SOUL_VC_STRIKE = sd->k_tick_c; return 0; }                sd->spamcount_AG_SOUL_VC_STRIKE = 0;                sd->spamtick_AG_SOUL_VC_STRIKE = tick + sd->kdelay;                break;
			case AG_STRANTUM_TREMOR:               if (k_tick_check(sd, sd->spamtick_AG_STRANTUM_TREMOR,               sd->spamcount_AG_STRANTUM_TREMOR,               battle_config.kd_AG_STRANTUM_TREMOR,               battle_config.kdw_AG_STRANTUM_TREMOR))               { sd->spamcount_AG_STRANTUM_TREMOR = sd->k_tick_c; return 0; }               sd->spamcount_AG_STRANTUM_TREMOR = 0;               sd->spamtick_AG_STRANTUM_TREMOR = tick + sd->kdelay;               break;
			case AG_ALL_BLOOM:                     if (k_tick_check(sd, sd->spamtick_AG_ALL_BLOOM,                     sd->spamcount_AG_ALL_BLOOM,                     battle_config.kd_AG_ALL_BLOOM,                     battle_config.kdw_AG_ALL_BLOOM))                     { sd->spamcount_AG_ALL_BLOOM = sd->k_tick_c; return 0; }                     sd->spamcount_AG_ALL_BLOOM = 0;                     sd->spamtick_AG_ALL_BLOOM = tick + sd->kdelay;                     break;
			case AG_CRYSTAL_IMPACT:                if (k_tick_check(sd, sd->spamtick_AG_CRYSTAL_IMPACT,                sd->spamcount_AG_CRYSTAL_IMPACT,                battle_config.kd_AG_CRYSTAL_IMPACT,                battle_config.kdw_AG_CRYSTAL_IMPACT))                { sd->spamcount_AG_CRYSTAL_IMPACT = sd->k_tick_c; return 0; }                sd->spamcount_AG_CRYSTAL_IMPACT = 0;                sd->spamtick_AG_CRYSTAL_IMPACT = tick + sd->kdelay;                break;
			case AG_TORNADO_STORM:                 if (k_tick_check(sd, sd->spamtick_AG_TORNADO_STORM,                 sd->spamcount_AG_TORNADO_STORM,                 battle_config.kd_AG_TORNADO_STORM,                 battle_config.kdw_AG_TORNADO_STORM))                 { sd->spamcount_AG_TORNADO_STORM = sd->k_tick_c; return 0; }                 sd->spamcount_AG_TORNADO_STORM = 0;                 sd->spamtick_AG_TORNADO_STORM = tick + sd->kdelay;                 break;
			case AG_FLORAL_FLARE_ROAD:             if (k_tick_check(sd, sd->spamtick_AG_FLORAL_FLARE_ROAD,             sd->spamcount_AG_FLORAL_FLARE_ROAD,             battle_config.kd_AG_FLORAL_FLARE_ROAD,             battle_config.kdw_AG_FLORAL_FLARE_ROAD))             { sd->spamcount_AG_FLORAL_FLARE_ROAD = sd->k_tick_c; return 0; }             sd->spamcount_AG_FLORAL_FLARE_ROAD = 0;             sd->spamtick_AG_FLORAL_FLARE_ROAD = tick + sd->kdelay;             break;
			case AG_ASTRAL_STRIKE:                 if (k_tick_check(sd, sd->spamtick_AG_ASTRAL_STRIKE,                 sd->spamcount_AG_ASTRAL_STRIKE,                 battle_config.kd_AG_ASTRAL_STRIKE,                 battle_config.kdw_AG_ASTRAL_STRIKE))                 { sd->spamcount_AG_ASTRAL_STRIKE = sd->k_tick_c; return 0; }                 sd->spamcount_AG_ASTRAL_STRIKE = 0;                 sd->spamtick_AG_ASTRAL_STRIKE = tick + sd->kdelay;                 break;
			case AG_CLIMAX:                        if (k_tick_check(sd, sd->spamtick_AG_CLIMAX,                        sd->spamcount_AG_CLIMAX,                        battle_config.kd_AG_CLIMAX,                        battle_config.kdw_AG_CLIMAX))                        { sd->spamcount_AG_CLIMAX = sd->k_tick_c; return 0; }                        sd->spamcount_AG_CLIMAX = 0;                        sd->spamtick_AG_CLIMAX = tick + sd->kdelay;                        break;
			case AG_ROCK_DOWN:                     if (k_tick_check(sd, sd->spamtick_AG_ROCK_DOWN,                     sd->spamcount_AG_ROCK_DOWN,                     battle_config.kd_AG_ROCK_DOWN,                     battle_config.kdw_AG_ROCK_DOWN))                     { sd->spamcount_AG_ROCK_DOWN = sd->k_tick_c; return 0; }                     sd->spamcount_AG_ROCK_DOWN = 0;                     sd->spamtick_AG_ROCK_DOWN = tick + sd->kdelay;                     break;
			case AG_STORM_CANNON:                  if (k_tick_check(sd, sd->spamtick_AG_STORM_CANNON,                  sd->spamcount_AG_STORM_CANNON,                  battle_config.kd_AG_STORM_CANNON,                  battle_config.kdw_AG_STORM_CANNON))                  { sd->spamcount_AG_STORM_CANNON = sd->k_tick_c; return 0; }                  sd->spamcount_AG_STORM_CANNON = 0;                  sd->spamtick_AG_STORM_CANNON = tick + sd->kdelay;                  break;
			case AG_CRIMSON_ARROW:                 if (k_tick_check(sd, sd->spamtick_AG_CRIMSON_ARROW,                 sd->spamcount_AG_CRIMSON_ARROW,                 battle_config.kd_AG_CRIMSON_ARROW,                 battle_config.kdw_AG_CRIMSON_ARROW))                 { sd->spamcount_AG_CRIMSON_ARROW = sd->k_tick_c; return 0; }                 sd->spamcount_AG_CRIMSON_ARROW = 0;                 sd->spamtick_AG_CRIMSON_ARROW = tick + sd->kdelay;                 break;
			case AG_FROZEN_SLASH:                  if (k_tick_check(sd, sd->spamtick_AG_FROZEN_SLASH,                  sd->spamcount_AG_FROZEN_SLASH,                  battle_config.kd_AG_FROZEN_SLASH,                  battle_config.kdw_AG_FROZEN_SLASH))                  { sd->spamcount_AG_FROZEN_SLASH = sd->k_tick_c; return 0; }                  sd->spamcount_AG_FROZEN_SLASH = 0;                  sd->spamtick_AG_FROZEN_SLASH = tick + sd->kdelay;                  break;
			case IQ_POWERFUL_FAITH:                if (k_tick_check(sd, sd->spamtick_IQ_POWERFUL_FAITH,                sd->spamcount_IQ_POWERFUL_FAITH,                battle_config.kd_IQ_POWERFUL_FAITH,                battle_config.kdw_IQ_POWERFUL_FAITH))                { sd->spamcount_IQ_POWERFUL_FAITH = sd->k_tick_c; return 0; }                sd->spamcount_IQ_POWERFUL_FAITH = 0;                sd->spamtick_IQ_POWERFUL_FAITH = tick + sd->kdelay;                break;
			case IQ_FIRM_FAITH:                    if (k_tick_check(sd, sd->spamtick_IQ_FIRM_FAITH,                    sd->spamcount_IQ_FIRM_FAITH,                    battle_config.kd_IQ_FIRM_FAITH,                    battle_config.kdw_IQ_FIRM_FAITH))                    { sd->spamcount_IQ_FIRM_FAITH = sd->k_tick_c; return 0; }                    sd->spamcount_IQ_FIRM_FAITH = 0;                    sd->spamtick_IQ_FIRM_FAITH = tick + sd->kdelay;                    break;
			case IQ_WILL_OF_FAITH:                 if (k_tick_check(sd, sd->spamtick_IQ_WILL_OF_FAITH,                 sd->spamcount_IQ_WILL_OF_FAITH,                 battle_config.kd_IQ_WILL_OF_FAITH,                 battle_config.kdw_IQ_WILL_OF_FAITH))                 { sd->spamcount_IQ_WILL_OF_FAITH = sd->k_tick_c; return 0; }                 sd->spamcount_IQ_WILL_OF_FAITH = 0;                 sd->spamtick_IQ_WILL_OF_FAITH = tick + sd->kdelay;                 break;
			case IQ_OLEUM_SANCTUM:                 if (k_tick_check(sd, sd->spamtick_IQ_OLEUM_SANCTUM,                 sd->spamcount_IQ_OLEUM_SANCTUM,                 battle_config.kd_IQ_OLEUM_SANCTUM,                 battle_config.kdw_IQ_OLEUM_SANCTUM))                 { sd->spamcount_IQ_OLEUM_SANCTUM = sd->k_tick_c; return 0; }                 sd->spamcount_IQ_OLEUM_SANCTUM = 0;                 sd->spamtick_IQ_OLEUM_SANCTUM = tick + sd->kdelay;                 break;
			case IQ_SINCERE_FAITH:                 if (k_tick_check(sd, sd->spamtick_IQ_SINCERE_FAITH,                 sd->spamcount_IQ_SINCERE_FAITH,                 battle_config.kd_IQ_SINCERE_FAITH,                 battle_config.kdw_IQ_SINCERE_FAITH))                 { sd->spamcount_IQ_SINCERE_FAITH = sd->k_tick_c; return 0; }                 sd->spamcount_IQ_SINCERE_FAITH = 0;                 sd->spamtick_IQ_SINCERE_FAITH = tick + sd->kdelay;                 break;
			case IQ_MASSIVE_F_BLASTER:             if (k_tick_check(sd, sd->spamtick_IQ_MASSIVE_F_BLASTER,             sd->spamcount_IQ_MASSIVE_F_BLASTER,             battle_config.kd_IQ_MASSIVE_F_BLASTER,             battle_config.kdw_IQ_MASSIVE_F_BLASTER))             { sd->spamcount_IQ_MASSIVE_F_BLASTER = sd->k_tick_c; return 0; }             sd->spamcount_IQ_MASSIVE_F_BLASTER = 0;             sd->spamtick_IQ_MASSIVE_F_BLASTER = tick + sd->kdelay;             break;
			case IQ_EXPOSION_BLASTER:              if (k_tick_check(sd, sd->spamtick_IQ_EXPOSION_BLASTER,              sd->spamcount_IQ_EXPOSION_BLASTER,              battle_config.kd_IQ_EXPOSION_BLASTER,              battle_config.kdw_IQ_EXPOSION_BLASTER))              { sd->spamcount_IQ_EXPOSION_BLASTER = sd->k_tick_c; return 0; }              sd->spamcount_IQ_EXPOSION_BLASTER = 0;              sd->spamtick_IQ_EXPOSION_BLASTER = tick + sd->kdelay;              break;
			case IQ_FIRST_BRAND:                   if (k_tick_check(sd, sd->spamtick_IQ_FIRST_BRAND,                   sd->spamcount_IQ_FIRST_BRAND,                   battle_config.kd_IQ_FIRST_BRAND,                   battle_config.kdw_IQ_FIRST_BRAND))                   { sd->spamcount_IQ_FIRST_BRAND = sd->k_tick_c; return 0; }                   sd->spamcount_IQ_FIRST_BRAND = 0;                   sd->spamtick_IQ_FIRST_BRAND = tick + sd->kdelay;                   break;
			case IQ_FIRST_FAITH_POWER:             if (k_tick_check(sd, sd->spamtick_IQ_FIRST_FAITH_POWER,             sd->spamcount_IQ_FIRST_FAITH_POWER,             battle_config.kd_IQ_FIRST_FAITH_POWER,             battle_config.kdw_IQ_FIRST_FAITH_POWER))             { sd->spamcount_IQ_FIRST_FAITH_POWER = sd->k_tick_c; return 0; }             sd->spamcount_IQ_FIRST_FAITH_POWER = 0;             sd->spamtick_IQ_FIRST_FAITH_POWER = tick + sd->kdelay;             break;
			case IQ_JUDGE:                         if (k_tick_check(sd, sd->spamtick_IQ_JUDGE,                         sd->spamcount_IQ_JUDGE,                         battle_config.kd_IQ_JUDGE,                         battle_config.kdw_IQ_JUDGE))                         { sd->spamcount_IQ_JUDGE = sd->k_tick_c; return 0; }                         sd->spamcount_IQ_JUDGE = 0;                         sd->spamtick_IQ_JUDGE = tick + sd->kdelay;                         break;
			case IQ_SECOND_FLAME:                  if (k_tick_check(sd, sd->spamtick_IQ_SECOND_FLAME,                  sd->spamcount_IQ_SECOND_FLAME,                  battle_config.kd_IQ_SECOND_FLAME,                  battle_config.kdw_IQ_SECOND_FLAME))                  { sd->spamcount_IQ_SECOND_FLAME = sd->k_tick_c; return 0; }                  sd->spamcount_IQ_SECOND_FLAME = 0;                  sd->spamtick_IQ_SECOND_FLAME = tick + sd->kdelay;                  break;
			case IQ_SECOND_FAITH:                  if (k_tick_check(sd, sd->spamtick_IQ_SECOND_FAITH,                  sd->spamcount_IQ_SECOND_FAITH,                  battle_config.kd_IQ_SECOND_FAITH,                  battle_config.kdw_IQ_SECOND_FAITH))                  { sd->spamcount_IQ_SECOND_FAITH = sd->k_tick_c; return 0; }                  sd->spamcount_IQ_SECOND_FAITH = 0;                  sd->spamtick_IQ_SECOND_FAITH = tick + sd->kdelay;                  break;
			case IQ_SECOND_JUDGEMENT:              if (k_tick_check(sd, sd->spamtick_IQ_SECOND_JUDGEMENT,              sd->spamcount_IQ_SECOND_JUDGEMENT,              battle_config.kd_IQ_SECOND_JUDGEMENT,              battle_config.kdw_IQ_SECOND_JUDGEMENT))              { sd->spamcount_IQ_SECOND_JUDGEMENT = sd->k_tick_c; return 0; }              sd->spamcount_IQ_SECOND_JUDGEMENT = 0;              sd->spamtick_IQ_SECOND_JUDGEMENT = tick + sd->kdelay;              break;
			case IQ_THIRD_PUNISH:                  if (k_tick_check(sd, sd->spamtick_IQ_THIRD_PUNISH,                  sd->spamcount_IQ_THIRD_PUNISH,                  battle_config.kd_IQ_THIRD_PUNISH,                  battle_config.kdw_IQ_THIRD_PUNISH))                  { sd->spamcount_IQ_THIRD_PUNISH = sd->k_tick_c; return 0; }                  sd->spamcount_IQ_THIRD_PUNISH = 0;                  sd->spamtick_IQ_THIRD_PUNISH = tick + sd->kdelay;                  break;
			case IQ_THIRD_FLAME_BOMB:              if (k_tick_check(sd, sd->spamtick_IQ_THIRD_FLAME_BOMB,              sd->spamcount_IQ_THIRD_FLAME_BOMB,              battle_config.kd_IQ_THIRD_FLAME_BOMB,              battle_config.kdw_IQ_THIRD_FLAME_BOMB))              { sd->spamcount_IQ_THIRD_FLAME_BOMB = sd->k_tick_c; return 0; }              sd->spamcount_IQ_THIRD_FLAME_BOMB = 0;              sd->spamtick_IQ_THIRD_FLAME_BOMB = tick + sd->kdelay;              break;
			case IQ_THIRD_CONSECRATION:            if (k_tick_check(sd, sd->spamtick_IQ_THIRD_CONSECRATION,            sd->spamcount_IQ_THIRD_CONSECRATION,            battle_config.kd_IQ_THIRD_CONSECRATION,            battle_config.kdw_IQ_THIRD_CONSECRATION))            { sd->spamcount_IQ_THIRD_CONSECRATION = sd->k_tick_c; return 0; }            sd->spamcount_IQ_THIRD_CONSECRATION = 0;            sd->spamtick_IQ_THIRD_CONSECRATION = tick + sd->kdelay;            break;
			case IQ_THIRD_EXOR_FLAME:              if (k_tick_check(sd, sd->spamtick_IQ_THIRD_EXOR_FLAME,              sd->spamcount_IQ_THIRD_EXOR_FLAME,              battle_config.kd_IQ_THIRD_EXOR_FLAME,              battle_config.kdw_IQ_THIRD_EXOR_FLAME))              { sd->spamcount_IQ_THIRD_EXOR_FLAME = sd->k_tick_c; return 0; }              sd->spamcount_IQ_THIRD_EXOR_FLAME = 0;              sd->spamtick_IQ_THIRD_EXOR_FLAME = tick + sd->kdelay;              break;
			case IG_GUARD_STANCE:                  if (k_tick_check(sd, sd->spamtick_IG_GUARD_STANCE,                  sd->spamcount_IG_GUARD_STANCE,                  battle_config.kd_IG_GUARD_STANCE,                  battle_config.kdw_IG_GUARD_STANCE))                  { sd->spamcount_IG_GUARD_STANCE = sd->k_tick_c; return 0; }                  sd->spamcount_IG_GUARD_STANCE = 0;                  sd->spamtick_IG_GUARD_STANCE = tick + sd->kdelay;                  break;
			case IG_GUARDIAN_SHIELD:               if (k_tick_check(sd, sd->spamtick_IG_GUARDIAN_SHIELD,               sd->spamcount_IG_GUARDIAN_SHIELD,               battle_config.kd_IG_GUARDIAN_SHIELD,               battle_config.kdw_IG_GUARDIAN_SHIELD))               { sd->spamcount_IG_GUARDIAN_SHIELD = sd->k_tick_c; return 0; }               sd->spamcount_IG_GUARDIAN_SHIELD = 0;               sd->spamtick_IG_GUARDIAN_SHIELD = tick + sd->kdelay;               break;
			case IG_REBOUND_SHIELD:                if (k_tick_check(sd, sd->spamtick_IG_REBOUND_SHIELD,                sd->spamcount_IG_REBOUND_SHIELD,                battle_config.kd_IG_REBOUND_SHIELD,                battle_config.kdw_IG_REBOUND_SHIELD))                { sd->spamcount_IG_REBOUND_SHIELD = sd->k_tick_c; return 0; }                sd->spamcount_IG_REBOUND_SHIELD = 0;                sd->spamtick_IG_REBOUND_SHIELD = tick + sd->kdelay;                break;
			case IG_ATTACK_STANCE:                 if (k_tick_check(sd, sd->spamtick_IG_ATTACK_STANCE,                 sd->spamcount_IG_ATTACK_STANCE,                 battle_config.kd_IG_ATTACK_STANCE,                 battle_config.kdw_IG_ATTACK_STANCE))                 { sd->spamcount_IG_ATTACK_STANCE = sd->k_tick_c; return 0; }                 sd->spamcount_IG_ATTACK_STANCE = 0;                 sd->spamtick_IG_ATTACK_STANCE = tick + sd->kdelay;                 break;
			case IG_ULTIMATE_SACRIFICE:            if (k_tick_check(sd, sd->spamtick_IG_ULTIMATE_SACRIFICE,            sd->spamcount_IG_ULTIMATE_SACRIFICE,            battle_config.kd_IG_ULTIMATE_SACRIFICE,            battle_config.kdw_IG_ULTIMATE_SACRIFICE))            { sd->spamcount_IG_ULTIMATE_SACRIFICE = sd->k_tick_c; return 0; }            sd->spamcount_IG_ULTIMATE_SACRIFICE = 0;            sd->spamtick_IG_ULTIMATE_SACRIFICE = tick + sd->kdelay;            break;
			case IG_HOLY_SHIELD:                   if (k_tick_check(sd, sd->spamtick_IG_HOLY_SHIELD,                   sd->spamcount_IG_HOLY_SHIELD,                   battle_config.kd_IG_HOLY_SHIELD,                   battle_config.kdw_IG_HOLY_SHIELD))                   { sd->spamcount_IG_HOLY_SHIELD = sd->k_tick_c; return 0; }                   sd->spamcount_IG_HOLY_SHIELD = 0;                   sd->spamtick_IG_HOLY_SHIELD = tick + sd->kdelay;                   break;
			case IG_GRAND_JUDGEMENT:               if (k_tick_check(sd, sd->spamtick_IG_GRAND_JUDGEMENT,               sd->spamcount_IG_GRAND_JUDGEMENT,               battle_config.kd_IG_GRAND_JUDGEMENT,               battle_config.kdw_IG_GRAND_JUDGEMENT))               { sd->spamcount_IG_GRAND_JUDGEMENT = sd->k_tick_c; return 0; }               sd->spamcount_IG_GRAND_JUDGEMENT = 0;               sd->spamtick_IG_GRAND_JUDGEMENT = tick + sd->kdelay;               break;
			case IG_JUDGEMENT_CROSS:               if (k_tick_check(sd, sd->spamtick_IG_JUDGEMENT_CROSS,               sd->spamcount_IG_JUDGEMENT_CROSS,               battle_config.kd_IG_JUDGEMENT_CROSS,               battle_config.kdw_IG_JUDGEMENT_CROSS))               { sd->spamcount_IG_JUDGEMENT_CROSS = sd->k_tick_c; return 0; }               sd->spamcount_IG_JUDGEMENT_CROSS = 0;               sd->spamtick_IG_JUDGEMENT_CROSS = tick + sd->kdelay;               break;
			case IG_SHIELD_SHOOTING:               if (k_tick_check(sd, sd->spamtick_IG_SHIELD_SHOOTING,               sd->spamcount_IG_SHIELD_SHOOTING,               battle_config.kd_IG_SHIELD_SHOOTING,               battle_config.kdw_IG_SHIELD_SHOOTING))               { sd->spamcount_IG_SHIELD_SHOOTING = sd->k_tick_c; return 0; }               sd->spamcount_IG_SHIELD_SHOOTING = 0;               sd->spamtick_IG_SHIELD_SHOOTING = tick + sd->kdelay;               break;
			case IG_OVERSLASH:                     if (k_tick_check(sd, sd->spamtick_IG_OVERSLASH,                     sd->spamcount_IG_OVERSLASH,                     battle_config.kd_IG_OVERSLASH,                     battle_config.kdw_IG_OVERSLASH))                     { sd->spamcount_IG_OVERSLASH = sd->k_tick_c; return 0; }                     sd->spamcount_IG_OVERSLASH = 0;                     sd->spamtick_IG_OVERSLASH = tick + sd->kdelay;                     break;
			case IG_CROSS_RAIN:                    if (k_tick_check(sd, sd->spamtick_IG_CROSS_RAIN,                    sd->spamcount_IG_CROSS_RAIN,                    battle_config.kd_IG_CROSS_RAIN,                    battle_config.kdw_IG_CROSS_RAIN))                    { sd->spamcount_IG_CROSS_RAIN = sd->k_tick_c; return 0; }                    sd->spamcount_IG_CROSS_RAIN = 0;                    sd->spamtick_IG_CROSS_RAIN = tick + sd->kdelay;                    break;
			case CD_REPARATIO:                     if (k_tick_check(sd, sd->spamtick_CD_REPARATIO,                     sd->spamcount_CD_REPARATIO,                     battle_config.kd_CD_REPARATIO,                     battle_config.kdw_CD_REPARATIO))                     { sd->spamcount_CD_REPARATIO = sd->k_tick_c; return 0; }                     sd->spamcount_CD_REPARATIO = 0;                     sd->spamtick_CD_REPARATIO = tick + sd->kdelay;                     break;
			case CD_MEDIALE_VOTUM:                 if (k_tick_check(sd, sd->spamtick_CD_MEDIALE_VOTUM,                 sd->spamcount_CD_MEDIALE_VOTUM,                 battle_config.kd_CD_MEDIALE_VOTUM,                 battle_config.kdw_CD_MEDIALE_VOTUM))                 { sd->spamcount_CD_MEDIALE_VOTUM = sd->k_tick_c; return 0; }                 sd->spamcount_CD_MEDIALE_VOTUM = 0;                 sd->spamtick_CD_MEDIALE_VOTUM = tick + sd->kdelay;                 break;
			case CD_ARGUTUS_VITA:                  if (k_tick_check(sd, sd->spamtick_CD_ARGUTUS_VITA,                  sd->spamcount_CD_ARGUTUS_VITA,                  battle_config.kd_CD_ARGUTUS_VITA,                  battle_config.kdw_CD_ARGUTUS_VITA))                  { sd->spamcount_CD_ARGUTUS_VITA = sd->k_tick_c; return 0; }                  sd->spamcount_CD_ARGUTUS_VITA = 0;                  sd->spamtick_CD_ARGUTUS_VITA = tick + sd->kdelay;                  break;
			case CD_ARGUTUS_TELUM:                 if (k_tick_check(sd, sd->spamtick_CD_ARGUTUS_TELUM,                 sd->spamcount_CD_ARGUTUS_TELUM,                 battle_config.kd_CD_ARGUTUS_TELUM,                 battle_config.kdw_CD_ARGUTUS_TELUM))                 { sd->spamcount_CD_ARGUTUS_TELUM = sd->k_tick_c; return 0; }                 sd->spamcount_CD_ARGUTUS_TELUM = 0;                 sd->spamtick_CD_ARGUTUS_TELUM = tick + sd->kdelay;                 break;
			case CD_ARBITRIUM:                     if (k_tick_check(sd, sd->spamtick_CD_ARBITRIUM,                     sd->spamcount_CD_ARBITRIUM,                     battle_config.kd_CD_ARBITRIUM,                     battle_config.kdw_CD_ARBITRIUM))                     { sd->spamcount_CD_ARBITRIUM = sd->k_tick_c; return 0; }                     sd->spamcount_CD_ARBITRIUM = 0;                     sd->spamtick_CD_ARBITRIUM = tick + sd->kdelay;                     break;
			case CD_PRESENS_ACIES:                 if (k_tick_check(sd, sd->spamtick_CD_PRESENS_ACIES,                 sd->spamcount_CD_PRESENS_ACIES,                 battle_config.kd_CD_PRESENS_ACIES,                 battle_config.kdw_CD_PRESENS_ACIES))                 { sd->spamcount_CD_PRESENS_ACIES = sd->k_tick_c; return 0; }                 sd->spamcount_CD_PRESENS_ACIES = 0;                 sd->spamtick_CD_PRESENS_ACIES = tick + sd->kdelay;                 break;
			case CD_EFFLIGO:                       if (k_tick_check(sd, sd->spamtick_CD_EFFLIGO,                       sd->spamcount_CD_EFFLIGO,                       battle_config.kd_CD_EFFLIGO,                       battle_config.kdw_CD_EFFLIGO))                       { sd->spamcount_CD_EFFLIGO = sd->k_tick_c; return 0; }                       sd->spamcount_CD_EFFLIGO = 0;                       sd->spamtick_CD_EFFLIGO = tick + sd->kdelay;                       break;
			case CD_COMPETENTIA:                   if (k_tick_check(sd, sd->spamtick_CD_COMPETENTIA,                   sd->spamcount_CD_COMPETENTIA,                   battle_config.kd_CD_COMPETENTIA,                   battle_config.kdw_CD_COMPETENTIA))                   { sd->spamcount_CD_COMPETENTIA = sd->k_tick_c; return 0; }                   sd->spamcount_CD_COMPETENTIA = 0;                   sd->spamtick_CD_COMPETENTIA = tick + sd->kdelay;                   break;
			case CD_PNEUMATICUS_PROCELLA:          if (k_tick_check(sd, sd->spamtick_CD_PNEUMATICUS_PROCELLA,          sd->spamcount_CD_PNEUMATICUS_PROCELLA,          battle_config.kd_CD_PNEUMATICUS_PROCELLA,          battle_config.kdw_CD_PNEUMATICUS_PROCELLA))          { sd->spamcount_CD_PNEUMATICUS_PROCELLA = sd->k_tick_c; return 0; }          sd->spamcount_CD_PNEUMATICUS_PROCELLA = 0;          sd->spamtick_CD_PNEUMATICUS_PROCELLA = tick + sd->kdelay;          break;
			case CD_DILECTIO_HEAL:                 if (k_tick_check(sd, sd->spamtick_CD_DILECTIO_HEAL,                 sd->spamcount_CD_DILECTIO_HEAL,                 battle_config.kd_CD_DILECTIO_HEAL,                 battle_config.kdw_CD_DILECTIO_HEAL))                 { sd->spamcount_CD_DILECTIO_HEAL = sd->k_tick_c; return 0; }                 sd->spamcount_CD_DILECTIO_HEAL = 0;                 sd->spamtick_CD_DILECTIO_HEAL = tick + sd->kdelay;                 break;
			case CD_RELIGIO:                       if (k_tick_check(sd, sd->spamtick_CD_RELIGIO,                       sd->spamcount_CD_RELIGIO,                       battle_config.kd_CD_RELIGIO,                       battle_config.kdw_CD_RELIGIO))                       { sd->spamcount_CD_RELIGIO = sd->k_tick_c; return 0; }                       sd->spamcount_CD_RELIGIO = 0;                       sd->spamtick_CD_RELIGIO = tick + sd->kdelay;                       break;
			case CD_BENEDICTUM:                    if (k_tick_check(sd, sd->spamtick_CD_BENEDICTUM,                    sd->spamcount_CD_BENEDICTUM,                    battle_config.kd_CD_BENEDICTUM,                    battle_config.kdw_CD_BENEDICTUM))                    { sd->spamcount_CD_BENEDICTUM = sd->k_tick_c; return 0; }                    sd->spamcount_CD_BENEDICTUM = 0;                    sd->spamtick_CD_BENEDICTUM = tick + sd->kdelay;                    break;
			case CD_PETITIO:                       if (k_tick_check(sd, sd->spamtick_CD_PETITIO,                       sd->spamcount_CD_PETITIO,                       battle_config.kd_CD_PETITIO,                       battle_config.kdw_CD_PETITIO))                       { sd->spamcount_CD_PETITIO = sd->k_tick_c; return 0; }                       sd->spamcount_CD_PETITIO = 0;                       sd->spamtick_CD_PETITIO = tick + sd->kdelay;                       break;
			case CD_FRAMEN:                        if (k_tick_check(sd, sd->spamtick_CD_FRAMEN,                        sd->spamcount_CD_FRAMEN,                        battle_config.kd_CD_FRAMEN,                        battle_config.kdw_CD_FRAMEN))                        { sd->spamcount_CD_FRAMEN = sd->k_tick_c; return 0; }                        sd->spamcount_CD_FRAMEN = 0;                        sd->spamtick_CD_FRAMEN = tick + sd->kdelay;                        break;
			case SHC_SHADOW_EXCEED:                if (k_tick_check(sd, sd->spamtick_SHC_SHADOW_EXCEED,                sd->spamcount_SHC_SHADOW_EXCEED,                battle_config.kd_SHC_SHADOW_EXCEED,                battle_config.kdw_SHC_SHADOW_EXCEED))                { sd->spamcount_SHC_SHADOW_EXCEED = sd->k_tick_c; return 0; }                sd->spamcount_SHC_SHADOW_EXCEED = 0;                sd->spamtick_SHC_SHADOW_EXCEED = tick + sd->kdelay;                break;
			case SHC_DANCING_KNIFE:                if (k_tick_check(sd, sd->spamtick_SHC_DANCING_KNIFE,                sd->spamcount_SHC_DANCING_KNIFE,                battle_config.kd_SHC_DANCING_KNIFE,                battle_config.kdw_SHC_DANCING_KNIFE))                { sd->spamcount_SHC_DANCING_KNIFE = sd->k_tick_c; return 0; }                sd->spamcount_SHC_DANCING_KNIFE = 0;                sd->spamtick_SHC_DANCING_KNIFE = tick + sd->kdelay;                break;
			case SHC_SAVAGE_IMPACT:                if (k_tick_check(sd, sd->spamtick_SHC_SAVAGE_IMPACT,                sd->spamcount_SHC_SAVAGE_IMPACT,                battle_config.kd_SHC_SAVAGE_IMPACT,                battle_config.kdw_SHC_SAVAGE_IMPACT))                { sd->spamcount_SHC_SAVAGE_IMPACT = sd->k_tick_c; return 0; }                sd->spamcount_SHC_SAVAGE_IMPACT = 0;                sd->spamtick_SHC_SAVAGE_IMPACT = tick + sd->kdelay;                break;
			case SHC_ETERNAL_SLASH:                if (k_tick_check(sd, sd->spamtick_SHC_ETERNAL_SLASH,                sd->spamcount_SHC_ETERNAL_SLASH,                battle_config.kd_SHC_ETERNAL_SLASH,                battle_config.kdw_SHC_ETERNAL_SLASH))                { sd->spamcount_SHC_ETERNAL_SLASH = sd->k_tick_c; return 0; }                sd->spamcount_SHC_ETERNAL_SLASH = 0;                sd->spamtick_SHC_ETERNAL_SLASH = tick + sd->kdelay;                break;
			case SHC_POTENT_VENOM:                 if (k_tick_check(sd, sd->spamtick_SHC_POTENT_VENOM,                 sd->spamcount_SHC_POTENT_VENOM,                 battle_config.kd_SHC_POTENT_VENOM,                 battle_config.kdw_SHC_POTENT_VENOM))                 { sd->spamcount_SHC_POTENT_VENOM = sd->k_tick_c; return 0; }                 sd->spamcount_SHC_POTENT_VENOM = 0;                 sd->spamtick_SHC_POTENT_VENOM = tick + sd->kdelay;                 break;
			case SHC_SHADOW_STAB:                  if (k_tick_check(sd, sd->spamtick_SHC_SHADOW_STAB,                  sd->spamcount_SHC_SHADOW_STAB,                  battle_config.kd_SHC_SHADOW_STAB,                  battle_config.kdw_SHC_SHADOW_STAB))                  { sd->spamcount_SHC_SHADOW_STAB = sd->k_tick_c; return 0; }                  sd->spamcount_SHC_SHADOW_STAB = 0;                  sd->spamtick_SHC_SHADOW_STAB = tick + sd->kdelay;                  break;
			case SHC_IMPACT_CRATER:                if (k_tick_check(sd, sd->spamtick_SHC_IMPACT_CRATER,                sd->spamcount_SHC_IMPACT_CRATER,                battle_config.kd_SHC_IMPACT_CRATER,                battle_config.kdw_SHC_IMPACT_CRATER))                { sd->spamcount_SHC_IMPACT_CRATER = sd->k_tick_c; return 0; }                sd->spamcount_SHC_IMPACT_CRATER = 0;                sd->spamtick_SHC_IMPACT_CRATER = tick + sd->kdelay;                break;
			case SHC_ENCHANTING_SHADOW:            if (k_tick_check(sd, sd->spamtick_SHC_ENCHANTING_SHADOW,            sd->spamcount_SHC_ENCHANTING_SHADOW,            battle_config.kd_SHC_ENCHANTING_SHADOW,            battle_config.kdw_SHC_ENCHANTING_SHADOW))            { sd->spamcount_SHC_ENCHANTING_SHADOW = sd->k_tick_c; return 0; }            sd->spamcount_SHC_ENCHANTING_SHADOW = 0;            sd->spamtick_SHC_ENCHANTING_SHADOW = tick + sd->kdelay;            break;
			case SHC_FATAL_SHADOW_CROW:            if (k_tick_check(sd, sd->spamtick_SHC_FATAL_SHADOW_CROW,            sd->spamcount_SHC_FATAL_SHADOW_CROW,            battle_config.kd_SHC_FATAL_SHADOW_CROW,            battle_config.kdw_SHC_FATAL_SHADOW_CROW))            { sd->spamcount_SHC_FATAL_SHADOW_CROW = sd->k_tick_c; return 0; }            sd->spamcount_SHC_FATAL_SHADOW_CROW = 0;            sd->spamtick_SHC_FATAL_SHADOW_CROW = tick + sd->kdelay;            break;
			case MT_AXE_STOMP:                     if (k_tick_check(sd, sd->spamtick_MT_AXE_STOMP,                     sd->spamcount_MT_AXE_STOMP,                     battle_config.kd_MT_AXE_STOMP,                     battle_config.kdw_MT_AXE_STOMP))                     { sd->spamcount_MT_AXE_STOMP = sd->k_tick_c; return 0; }                     sd->spamcount_MT_AXE_STOMP = 0;                     sd->spamtick_MT_AXE_STOMP = tick + sd->kdelay;                     break;
			case MT_RUSH_QUAKE:                    if (k_tick_check(sd, sd->spamtick_MT_RUSH_QUAKE,                    sd->spamcount_MT_RUSH_QUAKE,                    battle_config.kd_MT_RUSH_QUAKE,                    battle_config.kdw_MT_RUSH_QUAKE))                    { sd->spamcount_MT_RUSH_QUAKE = sd->k_tick_c; return 0; }                    sd->spamcount_MT_RUSH_QUAKE = 0;                    sd->spamtick_MT_RUSH_QUAKE = tick + sd->kdelay;                    break;
			case MT_M_MACHINE:                     if (k_tick_check(sd, sd->spamtick_MT_M_MACHINE,                     sd->spamcount_MT_M_MACHINE,                     battle_config.kd_MT_M_MACHINE,                     battle_config.kdw_MT_M_MACHINE))                     { sd->spamcount_MT_M_MACHINE = sd->k_tick_c; return 0; }                     sd->spamcount_MT_M_MACHINE = 0;                     sd->spamtick_MT_M_MACHINE = tick + sd->kdelay;                     break;
			case MT_A_MACHINE:                     if (k_tick_check(sd, sd->spamtick_MT_A_MACHINE,                     sd->spamcount_MT_A_MACHINE,                     battle_config.kd_MT_A_MACHINE,                     battle_config.kdw_MT_A_MACHINE))                     { sd->spamcount_MT_A_MACHINE = sd->k_tick_c; return 0; }                     sd->spamcount_MT_A_MACHINE = 0;                     sd->spamtick_MT_A_MACHINE = tick + sd->kdelay;                     break;
			case MT_D_MACHINE:                     if (k_tick_check(sd, sd->spamtick_MT_D_MACHINE,                     sd->spamcount_MT_D_MACHINE,                     battle_config.kd_MT_D_MACHINE,                     battle_config.kdw_MT_D_MACHINE))                     { sd->spamcount_MT_D_MACHINE = sd->k_tick_c; return 0; }                     sd->spamcount_MT_D_MACHINE = 0;                     sd->spamtick_MT_D_MACHINE = tick + sd->kdelay;                     break;
			case MT_TWOAXEDEF:                     if (k_tick_check(sd, sd->spamtick_MT_TWOAXEDEF,                     sd->spamcount_MT_TWOAXEDEF,                     battle_config.kd_MT_TWOAXEDEF,                     battle_config.kdw_MT_TWOAXEDEF))                     { sd->spamcount_MT_TWOAXEDEF = sd->k_tick_c; return 0; }                     sd->spamcount_MT_TWOAXEDEF = 0;                     sd->spamtick_MT_TWOAXEDEF = tick + sd->kdelay;                     break;
			case MT_ABR_M:                         if (k_tick_check(sd, sd->spamtick_MT_ABR_M,                         sd->spamcount_MT_ABR_M,                         battle_config.kd_MT_ABR_M,                         battle_config.kdw_MT_ABR_M))                         { sd->spamcount_MT_ABR_M = sd->k_tick_c; return 0; }                         sd->spamcount_MT_ABR_M = 0;                         sd->spamtick_MT_ABR_M = tick + sd->kdelay;                         break;
			case MT_SUMMON_ABR_BATTLE_WARIOR:      if (k_tick_check(sd, sd->spamtick_MT_SUMMON_ABR_BATTLE_WARIOR,      sd->spamcount_MT_SUMMON_ABR_BATTLE_WARIOR,      battle_config.kd_MT_SUMMON_ABR_BATTLE_WARIOR,      battle_config.kdw_MT_SUMMON_ABR_BATTLE_WARIOR))      { sd->spamcount_MT_SUMMON_ABR_BATTLE_WARIOR = sd->k_tick_c; return 0; }      sd->spamcount_MT_SUMMON_ABR_BATTLE_WARIOR = 0;      sd->spamtick_MT_SUMMON_ABR_BATTLE_WARIOR = tick + sd->kdelay;      break;
			case MT_SUMMON_ABR_DUAL_CANNON:        if (k_tick_check(sd, sd->spamtick_MT_SUMMON_ABR_DUAL_CANNON,        sd->spamcount_MT_SUMMON_ABR_DUAL_CANNON,        battle_config.kd_MT_SUMMON_ABR_DUAL_CANNON,        battle_config.kdw_MT_SUMMON_ABR_DUAL_CANNON))        { sd->spamcount_MT_SUMMON_ABR_DUAL_CANNON = sd->k_tick_c; return 0; }        sd->spamcount_MT_SUMMON_ABR_DUAL_CANNON = 0;        sd->spamtick_MT_SUMMON_ABR_DUAL_CANNON = tick + sd->kdelay;        break;
			case MT_SUMMON_ABR_MOTHER_NET:         if (k_tick_check(sd, sd->spamtick_MT_SUMMON_ABR_MOTHER_NET,         sd->spamcount_MT_SUMMON_ABR_MOTHER_NET,         battle_config.kd_MT_SUMMON_ABR_MOTHER_NET,         battle_config.kdw_MT_SUMMON_ABR_MOTHER_NET))         { sd->spamcount_MT_SUMMON_ABR_MOTHER_NET = sd->k_tick_c; return 0; }         sd->spamcount_MT_SUMMON_ABR_MOTHER_NET = 0;         sd->spamtick_MT_SUMMON_ABR_MOTHER_NET = tick + sd->kdelay;         break;
			case MT_SUMMON_ABR_INFINITY:           if (k_tick_check(sd, sd->spamtick_MT_SUMMON_ABR_INFINITY,           sd->spamcount_MT_SUMMON_ABR_INFINITY,           battle_config.kd_MT_SUMMON_ABR_INFINITY,           battle_config.kdw_MT_SUMMON_ABR_INFINITY))           { sd->spamcount_MT_SUMMON_ABR_INFINITY = sd->k_tick_c; return 0; }           sd->spamcount_MT_SUMMON_ABR_INFINITY = 0;           sd->spamtick_MT_SUMMON_ABR_INFINITY = tick + sd->kdelay;           break;
			case AG_DESTRUCTIVE_HURRICANE_CLIMAX:  if (k_tick_check(sd, sd->spamtick_AG_DESTRUCTIVE_HURRICANE_CLIMAX,  sd->spamcount_AG_DESTRUCTIVE_HURRICANE_CLIMAX,  battle_config.kd_AG_DESTRUCTIVE_HURRICANE_CLIMAX,  battle_config.kdw_AG_DESTRUCTIVE_HURRICANE_CLIMAX))  { sd->spamcount_AG_DESTRUCTIVE_HURRICANE_CLIMAX = sd->k_tick_c; return 0; }  sd->spamcount_AG_DESTRUCTIVE_HURRICANE_CLIMAX = 0;  sd->spamtick_AG_DESTRUCTIVE_HURRICANE_CLIMAX = tick + sd->kdelay;  break;
			case ABC_STRIP_SHADOW:                 if (k_tick_check(sd, sd->spamtick_ABC_STRIP_SHADOW,                 sd->spamcount_ABC_STRIP_SHADOW,                 battle_config.kd_ABC_STRIP_SHADOW,                 battle_config.kdw_ABC_STRIP_SHADOW))                 { sd->spamcount_ABC_STRIP_SHADOW = sd->k_tick_c; return 0; }                 sd->spamcount_ABC_STRIP_SHADOW = 0;                 sd->spamtick_ABC_STRIP_SHADOW = tick + sd->kdelay;                 break;
			case ABC_ABYSS_DAGGER:                 if (k_tick_check(sd, sd->spamtick_ABC_ABYSS_DAGGER,                 sd->spamcount_ABC_ABYSS_DAGGER,                 battle_config.kd_ABC_ABYSS_DAGGER,                 battle_config.kdw_ABC_ABYSS_DAGGER))                 { sd->spamcount_ABC_ABYSS_DAGGER = sd->k_tick_c; return 0; }                 sd->spamcount_ABC_ABYSS_DAGGER = 0;                 sd->spamtick_ABC_ABYSS_DAGGER = tick + sd->kdelay;                 break;
			case ABC_UNLUCKY_RUSH:                 if (k_tick_check(sd, sd->spamtick_ABC_UNLUCKY_RUSH,                 sd->spamcount_ABC_UNLUCKY_RUSH,                 battle_config.kd_ABC_UNLUCKY_RUSH,                 battle_config.kdw_ABC_UNLUCKY_RUSH))                 { sd->spamcount_ABC_UNLUCKY_RUSH = sd->k_tick_c; return 0; }                 sd->spamcount_ABC_UNLUCKY_RUSH = 0;                 sd->spamtick_ABC_UNLUCKY_RUSH = tick + sd->kdelay;                 break;
			case ABC_CHAIN_REACTION_SHOT:          if (k_tick_check(sd, sd->spamtick_ABC_CHAIN_REACTION_SHOT,          sd->spamcount_ABC_CHAIN_REACTION_SHOT,          battle_config.kd_ABC_CHAIN_REACTION_SHOT,          battle_config.kdw_ABC_CHAIN_REACTION_SHOT))          { sd->spamcount_ABC_CHAIN_REACTION_SHOT = sd->k_tick_c; return 0; }          sd->spamcount_ABC_CHAIN_REACTION_SHOT = 0;          sd->spamtick_ABC_CHAIN_REACTION_SHOT = tick + sd->kdelay;          break;
			case ABC_FROM_THE_ABYSS:               if (k_tick_check(sd, sd->spamtick_ABC_FROM_THE_ABYSS,               sd->spamcount_ABC_FROM_THE_ABYSS,               battle_config.kd_ABC_FROM_THE_ABYSS,               battle_config.kdw_ABC_FROM_THE_ABYSS))               { sd->spamcount_ABC_FROM_THE_ABYSS = sd->k_tick_c; return 0; }               sd->spamcount_ABC_FROM_THE_ABYSS = 0;               sd->spamtick_ABC_FROM_THE_ABYSS = tick + sd->kdelay;               break;
			case ABC_ABYSS_SLAYER:                 if (k_tick_check(sd, sd->spamtick_ABC_ABYSS_SLAYER,                 sd->spamcount_ABC_ABYSS_SLAYER,                 battle_config.kd_ABC_ABYSS_SLAYER,                 battle_config.kdw_ABC_ABYSS_SLAYER))                 { sd->spamcount_ABC_ABYSS_SLAYER = sd->k_tick_c; return 0; }                 sd->spamcount_ABC_ABYSS_SLAYER = 0;                 sd->spamtick_ABC_ABYSS_SLAYER = tick + sd->kdelay;                 break;
			case ABC_ABYSS_STRIKE:                 if (k_tick_check(sd, sd->spamtick_ABC_ABYSS_STRIKE,                 sd->spamcount_ABC_ABYSS_STRIKE,                 battle_config.kd_ABC_ABYSS_STRIKE,                 battle_config.kdw_ABC_ABYSS_STRIKE))                 { sd->spamcount_ABC_ABYSS_STRIKE = sd->k_tick_c; return 0; }                 sd->spamcount_ABC_ABYSS_STRIKE = 0;                 sd->spamtick_ABC_ABYSS_STRIKE = tick + sd->kdelay;                 break;
			case ABC_DEFT_STAB:                    if (k_tick_check(sd, sd->spamtick_ABC_DEFT_STAB,                    sd->spamcount_ABC_DEFT_STAB,                    battle_config.kd_ABC_DEFT_STAB,                    battle_config.kdw_ABC_DEFT_STAB))                    { sd->spamcount_ABC_DEFT_STAB = sd->k_tick_c; return 0; }                    sd->spamcount_ABC_DEFT_STAB = 0;                    sd->spamtick_ABC_DEFT_STAB = tick + sd->kdelay;                    break;
			case ABC_ABYSS_SQUARE:                 if (k_tick_check(sd, sd->spamtick_ABC_ABYSS_SQUARE,                 sd->spamcount_ABC_ABYSS_SQUARE,                 battle_config.kd_ABC_ABYSS_SQUARE,                 battle_config.kdw_ABC_ABYSS_SQUARE))                 { sd->spamcount_ABC_ABYSS_SQUARE = sd->k_tick_c; return 0; }                 sd->spamcount_ABC_ABYSS_SQUARE = 0;                 sd->spamtick_ABC_ABYSS_SQUARE = tick + sd->kdelay;                 break;
			case ABC_FRENZY_SHOT:                  if (k_tick_check(sd, sd->spamtick_ABC_FRENZY_SHOT,                  sd->spamcount_ABC_FRENZY_SHOT,                  battle_config.kd_ABC_FRENZY_SHOT,                  battle_config.kdw_ABC_FRENZY_SHOT))                  { sd->spamcount_ABC_FRENZY_SHOT = sd->k_tick_c; return 0; }                  sd->spamcount_ABC_FRENZY_SHOT = 0;                  sd->spamtick_ABC_FRENZY_SHOT = tick + sd->kdelay;                  break;
			case WH_NATUREFRIENDLY:                if (k_tick_check(sd, sd->spamtick_WH_NATUREFRIENDLY,                sd->spamcount_WH_NATUREFRIENDLY,                battle_config.kd_WH_NATUREFRIENDLY,                battle_config.kdw_WH_NATUREFRIENDLY))                { sd->spamcount_WH_NATUREFRIENDLY = sd->k_tick_c; return 0; }                sd->spamcount_WH_NATUREFRIENDLY = 0;                sd->spamtick_WH_NATUREFRIENDLY = tick + sd->kdelay;                break;
			case WH_HAWKRUSH:                      if (k_tick_check(sd, sd->spamtick_WH_HAWKRUSH,                      sd->spamcount_WH_HAWKRUSH,                      battle_config.kd_WH_HAWKRUSH,                      battle_config.kdw_WH_HAWKRUSH))                      { sd->spamcount_WH_HAWKRUSH = sd->k_tick_c; return 0; }                      sd->spamcount_WH_HAWKRUSH = 0;                      sd->spamtick_WH_HAWKRUSH = tick + sd->kdelay;                      break;
			case WH_HAWKBOOMERANG:                 if (k_tick_check(sd, sd->spamtick_WH_HAWKBOOMERANG,                 sd->spamcount_WH_HAWKBOOMERANG,                 battle_config.kd_WH_HAWKBOOMERANG,                 battle_config.kdw_WH_HAWKBOOMERANG))                 { sd->spamcount_WH_HAWKBOOMERANG = sd->k_tick_c; return 0; }                 sd->spamcount_WH_HAWKBOOMERANG = 0;                 sd->spamtick_WH_HAWKBOOMERANG = tick + sd->kdelay;                 break;
			case WH_GALESTORM:                     if (k_tick_check(sd, sd->spamtick_WH_GALESTORM,                     sd->spamcount_WH_GALESTORM,                     battle_config.kd_WH_GALESTORM,                     battle_config.kdw_WH_GALESTORM))                     { sd->spamcount_WH_GALESTORM = sd->k_tick_c; return 0; }                     sd->spamcount_WH_GALESTORM = 0;                     sd->spamtick_WH_GALESTORM = tick + sd->kdelay;                     break;
			case WH_DEEPBLINDTRAP:                 if (k_tick_check(sd, sd->spamtick_WH_DEEPBLINDTRAP,                 sd->spamcount_WH_DEEPBLINDTRAP,                 battle_config.kd_WH_DEEPBLINDTRAP,                 battle_config.kdw_WH_DEEPBLINDTRAP))                 { sd->spamcount_WH_DEEPBLINDTRAP = sd->k_tick_c; return 0; }                 sd->spamcount_WH_DEEPBLINDTRAP = 0;                 sd->spamtick_WH_DEEPBLINDTRAP = tick + sd->kdelay;                 break;
			case WH_SOLIDTRAP:                     if (k_tick_check(sd, sd->spamtick_WH_SOLIDTRAP,                     sd->spamcount_WH_SOLIDTRAP,                     battle_config.kd_WH_SOLIDTRAP,                     battle_config.kdw_WH_SOLIDTRAP))                     { sd->spamcount_WH_SOLIDTRAP = sd->k_tick_c; return 0; }                     sd->spamcount_WH_SOLIDTRAP = 0;                     sd->spamtick_WH_SOLIDTRAP = tick + sd->kdelay;                     break;
			case WH_SWIFTTRAP:                     if (k_tick_check(sd, sd->spamtick_WH_SWIFTTRAP,                     sd->spamcount_WH_SWIFTTRAP,                     battle_config.kd_WH_SWIFTTRAP,                     battle_config.kdw_WH_SWIFTTRAP))                     { sd->spamcount_WH_SWIFTTRAP = sd->k_tick_c; return 0; }                     sd->spamcount_WH_SWIFTTRAP = 0;                     sd->spamtick_WH_SWIFTTRAP = tick + sd->kdelay;                     break;
			case WH_CRESCIVE_BOLT:                 if (k_tick_check(sd, sd->spamtick_WH_CRESCIVE_BOLT,                 sd->spamcount_WH_CRESCIVE_BOLT,                 battle_config.kd_WH_CRESCIVE_BOLT,                 battle_config.kdw_WH_CRESCIVE_BOLT))                 { sd->spamcount_WH_CRESCIVE_BOLT = sd->k_tick_c; return 0; }                 sd->spamcount_WH_CRESCIVE_BOLT = 0;                 sd->spamtick_WH_CRESCIVE_BOLT = tick + sd->kdelay;                 break;
			case WH_FLAMETRAP:                     if (k_tick_check(sd, sd->spamtick_WH_FLAMETRAP,                     sd->spamcount_WH_FLAMETRAP,                     battle_config.kd_WH_FLAMETRAP,                     battle_config.kdw_WH_FLAMETRAP))                     { sd->spamcount_WH_FLAMETRAP = sd->k_tick_c; return 0; }                     sd->spamcount_WH_FLAMETRAP = 0;                     sd->spamtick_WH_FLAMETRAP = tick + sd->kdelay;                     break;
			case BO_ACIDIFIED_ZONE_WATER:          if (k_tick_check(sd, sd->spamtick_BO_ACIDIFIED_ZONE_WATER,          sd->spamcount_BO_ACIDIFIED_ZONE_WATER,          battle_config.kd_BO_ACIDIFIED_ZONE_WATER,          battle_config.kdw_BO_ACIDIFIED_ZONE_WATER))          { sd->spamcount_BO_ACIDIFIED_ZONE_WATER = sd->k_tick_c; return 0; }          sd->spamcount_BO_ACIDIFIED_ZONE_WATER = 0;          sd->spamtick_BO_ACIDIFIED_ZONE_WATER = tick + sd->kdelay;          break;
			case BO_ACIDIFIED_ZONE_GROUND:         if (k_tick_check(sd, sd->spamtick_BO_ACIDIFIED_ZONE_GROUND,         sd->spamcount_BO_ACIDIFIED_ZONE_GROUND,         battle_config.kd_BO_ACIDIFIED_ZONE_GROUND,         battle_config.kdw_BO_ACIDIFIED_ZONE_GROUND))         { sd->spamcount_BO_ACIDIFIED_ZONE_GROUND = sd->k_tick_c; return 0; }         sd->spamcount_BO_ACIDIFIED_ZONE_GROUND = 0;         sd->spamtick_BO_ACIDIFIED_ZONE_GROUND = tick + sd->kdelay;         break;
			case BO_ACIDIFIED_ZONE_WIND:           if (k_tick_check(sd, sd->spamtick_BO_ACIDIFIED_ZONE_WIND,           sd->spamcount_BO_ACIDIFIED_ZONE_WIND,           battle_config.kd_BO_ACIDIFIED_ZONE_WIND,           battle_config.kdw_BO_ACIDIFIED_ZONE_WIND))           { sd->spamcount_BO_ACIDIFIED_ZONE_WIND = sd->k_tick_c; return 0; }           sd->spamcount_BO_ACIDIFIED_ZONE_WIND = 0;           sd->spamtick_BO_ACIDIFIED_ZONE_WIND = tick + sd->kdelay;           break;
			case BO_ACIDIFIED_ZONE_FIRE:           if (k_tick_check(sd, sd->spamtick_BO_ACIDIFIED_ZONE_FIRE,           sd->spamcount_BO_ACIDIFIED_ZONE_FIRE,           battle_config.kd_BO_ACIDIFIED_ZONE_FIRE,           battle_config.kdw_BO_ACIDIFIED_ZONE_FIRE))           { sd->spamcount_BO_ACIDIFIED_ZONE_FIRE = sd->k_tick_c; return 0; }           sd->spamcount_BO_ACIDIFIED_ZONE_FIRE = 0;           sd->spamtick_BO_ACIDIFIED_ZONE_FIRE = tick + sd->kdelay;           break;
			case TR_STAGE_MANNER:                  if (k_tick_check(sd, sd->spamtick_TR_STAGE_MANNER,                  sd->spamcount_TR_STAGE_MANNER,                  battle_config.kd_TR_STAGE_MANNER,                  battle_config.kdw_TR_STAGE_MANNER))                  { sd->spamcount_TR_STAGE_MANNER = sd->k_tick_c; return 0; }                  sd->spamcount_TR_STAGE_MANNER = 0;                  sd->spamtick_TR_STAGE_MANNER = tick + sd->kdelay;                  break;
			case TR_ROSEBLOSSOM:                   if (k_tick_check(sd, sd->spamtick_TR_ROSEBLOSSOM,                   sd->spamcount_TR_ROSEBLOSSOM,                   battle_config.kd_TR_ROSEBLOSSOM,                   battle_config.kdw_TR_ROSEBLOSSOM))                   { sd->spamcount_TR_ROSEBLOSSOM = sd->k_tick_c; return 0; }                   sd->spamcount_TR_ROSEBLOSSOM = 0;                   sd->spamtick_TR_ROSEBLOSSOM = tick + sd->kdelay;                   break;
			case TR_RHYTHMSHOOTING:                if (k_tick_check(sd, sd->spamtick_TR_RHYTHMSHOOTING,                sd->spamcount_TR_RHYTHMSHOOTING,                battle_config.kd_TR_RHYTHMSHOOTING,                battle_config.kdw_TR_RHYTHMSHOOTING))                { sd->spamcount_TR_RHYTHMSHOOTING = sd->k_tick_c; return 0; }                sd->spamcount_TR_RHYTHMSHOOTING = 0;                sd->spamtick_TR_RHYTHMSHOOTING = tick + sd->kdelay;                break;
			case TR_METALIC_FURY:                  if (k_tick_check(sd, sd->spamtick_TR_METALIC_FURY,                  sd->spamcount_TR_METALIC_FURY,                  battle_config.kd_TR_METALIC_FURY,                  battle_config.kdw_TR_METALIC_FURY))                  { sd->spamcount_TR_METALIC_FURY = sd->k_tick_c; return 0; }                  sd->spamcount_TR_METALIC_FURY = 0;                  sd->spamtick_TR_METALIC_FURY = tick + sd->kdelay;                  break;
			case EM_DIAMOND_STORM:                 if (k_tick_check(sd, sd->spamtick_EM_DIAMOND_STORM,                 sd->spamcount_EM_DIAMOND_STORM,                 battle_config.kd_EM_DIAMOND_STORM,                 battle_config.kdw_EM_DIAMOND_STORM))                 { sd->spamcount_EM_DIAMOND_STORM = sd->k_tick_c; return 0; }                 sd->spamcount_EM_DIAMOND_STORM = 0;                 sd->spamtick_EM_DIAMOND_STORM = tick + sd->kdelay;                 break;
			case EM_LIGHTNING_LAND:                if (k_tick_check(sd, sd->spamtick_EM_LIGHTNING_LAND,                sd->spamcount_EM_LIGHTNING_LAND,                battle_config.kd_EM_LIGHTNING_LAND,                battle_config.kdw_EM_LIGHTNING_LAND))                { sd->spamcount_EM_LIGHTNING_LAND = sd->k_tick_c; return 0; }                sd->spamcount_EM_LIGHTNING_LAND = 0;                sd->spamtick_EM_LIGHTNING_LAND = tick + sd->kdelay;                break;
			case EM_VENOM_SWAMP:                   if (k_tick_check(sd, sd->spamtick_EM_VENOM_SWAMP,                   sd->spamcount_EM_VENOM_SWAMP,                   battle_config.kd_EM_VENOM_SWAMP,                   battle_config.kdw_EM_VENOM_SWAMP))                   { sd->spamcount_EM_VENOM_SWAMP = sd->k_tick_c; return 0; }                   sd->spamcount_EM_VENOM_SWAMP = 0;                   sd->spamtick_EM_VENOM_SWAMP = tick + sd->kdelay;                   break;
			case EM_CONFLAGRATION:                 if (k_tick_check(sd, sd->spamtick_EM_CONFLAGRATION,                 sd->spamcount_EM_CONFLAGRATION,                 battle_config.kd_EM_CONFLAGRATION,                 battle_config.kdw_EM_CONFLAGRATION))                 { sd->spamcount_EM_CONFLAGRATION = sd->k_tick_c; return 0; }                 sd->spamcount_EM_CONFLAGRATION = 0;                 sd->spamtick_EM_CONFLAGRATION = tick + sd->kdelay;                 break;
			case EM_TERRA_DRIVE:                   if (k_tick_check(sd, sd->spamtick_EM_TERRA_DRIVE,                   sd->spamcount_EM_TERRA_DRIVE,                   battle_config.kd_EM_TERRA_DRIVE,                   battle_config.kdw_EM_TERRA_DRIVE))                   { sd->spamcount_EM_TERRA_DRIVE = sd->k_tick_c; return 0; }                   sd->spamcount_EM_TERRA_DRIVE = 0;                   sd->spamtick_EM_TERRA_DRIVE = tick + sd->kdelay;                   break;
			case EM_ELEMENTAL_BUSTER:              if (k_tick_check(sd, sd->spamtick_EM_ELEMENTAL_BUSTER,              sd->spamcount_EM_ELEMENTAL_BUSTER,              battle_config.kd_EM_ELEMENTAL_BUSTER,              battle_config.kdw_EM_ELEMENTAL_BUSTER))              { sd->spamcount_EM_ELEMENTAL_BUSTER = sd->k_tick_c; return 0; }              sd->spamcount_EM_ELEMENTAL_BUSTER = 0;              sd->spamtick_EM_ELEMENTAL_BUSTER = tick + sd->kdelay;              break;
			case BO_WOODEN_THROWROCK:              if (k_tick_check(sd, sd->spamtick_BO_WOODEN_THROWROCK,              sd->spamcount_BO_WOODEN_THROWROCK,              battle_config.kd_BO_WOODEN_THROWROCK,              battle_config.kdw_BO_WOODEN_THROWROCK))              { sd->spamcount_BO_WOODEN_THROWROCK = sd->k_tick_c; return 0; }              sd->spamcount_BO_WOODEN_THROWROCK = 0;              sd->spamtick_BO_WOODEN_THROWROCK = tick + sd->kdelay;              break;
			case BO_WOODEN_ATTACK:                 if (k_tick_check(sd, sd->spamtick_BO_WOODEN_ATTACK,                 sd->spamcount_BO_WOODEN_ATTACK,                 battle_config.kd_BO_WOODEN_ATTACK,                 battle_config.kdw_BO_WOODEN_ATTACK))                 { sd->spamcount_BO_WOODEN_ATTACK = sd->k_tick_c; return 0; }                 sd->spamcount_BO_WOODEN_ATTACK = 0;                 sd->spamtick_BO_WOODEN_ATTACK = tick + sd->kdelay;                 break;
			case BO_HELL_HOWLING:                  if (k_tick_check(sd, sd->spamtick_BO_HELL_HOWLING,                  sd->spamcount_BO_HELL_HOWLING,                  battle_config.kd_BO_HELL_HOWLING,                  battle_config.kdw_BO_HELL_HOWLING))                  { sd->spamcount_BO_HELL_HOWLING = sd->k_tick_c; return 0; }                  sd->spamcount_BO_HELL_HOWLING = 0;                  sd->spamtick_BO_HELL_HOWLING = tick + sd->kdelay;                  break;
			case BO_HELL_DUSTY:                    if (k_tick_check(sd, sd->spamtick_BO_HELL_DUSTY,                    sd->spamcount_BO_HELL_DUSTY,                    battle_config.kd_BO_HELL_DUSTY,                    battle_config.kdw_BO_HELL_DUSTY))                    { sd->spamcount_BO_HELL_DUSTY = sd->k_tick_c; return 0; }                    sd->spamcount_BO_HELL_DUSTY = 0;                    sd->spamtick_BO_HELL_DUSTY = tick + sd->kdelay;                    break;
			case BO_FAIRY_DUSTY:                   if (k_tick_check(sd, sd->spamtick_BO_FAIRY_DUSTY,                   sd->spamcount_BO_FAIRY_DUSTY,                   battle_config.kd_BO_FAIRY_DUSTY,                   battle_config.kdw_BO_FAIRY_DUSTY))                   { sd->spamcount_BO_FAIRY_DUSTY = sd->k_tick_c; return 0; }                   sd->spamcount_BO_FAIRY_DUSTY = 0;                   sd->spamtick_BO_FAIRY_DUSTY = tick + sd->kdelay;                   break;
			case EM_ELEMENTAL_BUSTER_FIRE:         if (k_tick_check(sd, sd->spamtick_EM_ELEMENTAL_BUSTER_FIRE,         sd->spamcount_EM_ELEMENTAL_BUSTER_FIRE,         battle_config.kd_EM_ELEMENTAL_BUSTER_FIRE,         battle_config.kdw_EM_ELEMENTAL_BUSTER_FIRE))         { sd->spamcount_EM_ELEMENTAL_BUSTER_FIRE = sd->k_tick_c; return 0; }         sd->spamcount_EM_ELEMENTAL_BUSTER_FIRE = 0;         sd->spamtick_EM_ELEMENTAL_BUSTER_FIRE = tick + sd->kdelay;         break;
			case EM_ELEMENTAL_BUSTER_WATER:        if (k_tick_check(sd, sd->spamtick_EM_ELEMENTAL_BUSTER_WATER,        sd->spamcount_EM_ELEMENTAL_BUSTER_WATER,        battle_config.kd_EM_ELEMENTAL_BUSTER_WATER,        battle_config.kdw_EM_ELEMENTAL_BUSTER_WATER))        { sd->spamcount_EM_ELEMENTAL_BUSTER_WATER = sd->k_tick_c; return 0; }        sd->spamcount_EM_ELEMENTAL_BUSTER_WATER = 0;        sd->spamtick_EM_ELEMENTAL_BUSTER_WATER = tick + sd->kdelay;        break;
			case EM_ELEMENTAL_BUSTER_WIND:         if (k_tick_check(sd, sd->spamtick_EM_ELEMENTAL_BUSTER_WIND,         sd->spamcount_EM_ELEMENTAL_BUSTER_WIND,         battle_config.kd_EM_ELEMENTAL_BUSTER_WIND,         battle_config.kdw_EM_ELEMENTAL_BUSTER_WIND))         { sd->spamcount_EM_ELEMENTAL_BUSTER_WIND = sd->k_tick_c; return 0; }         sd->spamcount_EM_ELEMENTAL_BUSTER_WIND = 0;         sd->spamtick_EM_ELEMENTAL_BUSTER_WIND = tick + sd->kdelay;         break;
			case EM_ELEMENTAL_BUSTER_GROUND:       if (k_tick_check(sd, sd->spamtick_EM_ELEMENTAL_BUSTER_GROUND,       sd->spamcount_EM_ELEMENTAL_BUSTER_GROUND,       battle_config.kd_EM_ELEMENTAL_BUSTER_GROUND,       battle_config.kdw_EM_ELEMENTAL_BUSTER_GROUND))       { sd->spamcount_EM_ELEMENTAL_BUSTER_GROUND = sd->k_tick_c; return 0; }       sd->spamcount_EM_ELEMENTAL_BUSTER_GROUND = 0;       sd->spamtick_EM_ELEMENTAL_BUSTER_GROUND = tick + sd->kdelay;       break;
			case EM_ELEMENTAL_BUSTER_POISON:       if (k_tick_check(sd, sd->spamtick_EM_ELEMENTAL_BUSTER_POISON,       sd->spamcount_EM_ELEMENTAL_BUSTER_POISON,       battle_config.kd_EM_ELEMENTAL_BUSTER_POISON,       battle_config.kdw_EM_ELEMENTAL_BUSTER_POISON))       { sd->spamcount_EM_ELEMENTAL_BUSTER_POISON = sd->k_tick_c; return 0; }       sd->spamcount_EM_ELEMENTAL_BUSTER_POISON = 0;       sd->spamtick_EM_ELEMENTAL_BUSTER_POISON = tick + sd->kdelay;       break;
			default:
				if (k_tick_check(sd, sd->spamtick_DEFAULT, sd->spamcount_DEFAULT, battle_config.kd_DEFAULT, battle_config.kdw_DEFAULT)) {
					sd->spamcount_DEFAULT = sd->k_tick_c;
					return 0;
				}
				sd->spamcount_DEFAULT = 0;
				sd->spamtick_DEFAULT = tick + sd->kdelay;
				break;
			}
		}

		skill_castend_id(ud->skilltimer, tick, src->id, 0);
	}

	if( sd && battle_config.prevent_logout_trigger&PLT_SKILL )
		sd->canlog_tick = gettick();

	return 1;
}

/**
 * Initiates a placement (ground/non-targeted) skill
 * @param src: Object using skill
 * @param skill_x: X coordinate where skill is being casted (center)
 * @param skill_y: Y coordinate where skill is being casted (center)
 * @param skill_id: Skill ID
 * @param skill_lv: Skill Level
 * @return unit_skilluse_pos2()
 */
int32 unit_skilluse_pos(struct block_list *src, int16 skill_x, int16 skill_y, uint16 skill_id, uint16 skill_lv)
{
	return unit_skilluse_pos2(
		src, skill_x, skill_y, skill_id, skill_lv,
		skill_castfix(src, skill_id, skill_lv),
		skill_get_castcancel(skill_id)
	);
}

/**
 * Performs checks for a unit using a skill and executes after cast time completion
 * @param src: Object using skill
 * @param skill_x: X coordinate where skill is being casted (center)
 * @param skill_y: Y coordinate where skill is being casted (center)
 * @param skill_id: Skill ID
 * @param skill_lv: Skill Level
 * @param casttime: Initial cast time before cast time reductions
 * @param castcancel: Whether or not the skill can be cancelled by interuption (hit)
 * @return Success(1); Fail(0);
 */
int32 unit_skilluse_pos2( struct block_list *src, int16 skill_x, int16 skill_y, uint16 skill_id, uint16 skill_lv, int32 casttime, int32 castcancel, bool ignore_range)
{
	map_session_data *sd = nullptr;
	struct unit_data *ud = nullptr;
	status_change *sc;
	struct block_list bl;
	t_tick tick = gettick();
	int32 range;

	nullpo_ret(src);

	if (!src->prev)
		return 0; // Not on the map

	if(status_isdead(*src))
		return 0;

	sd = BL_CAST(BL_PC, src);
	ud = unit_bl2ud(src);

	if(ud == nullptr)
		return 0;

	if (ud && ud->state.blockedskill)
		return 0;

	if(ud->skilltimer != INVALID_TIMER) // Normally not needed since clif.cpp checks for it, but at/char/script commands don't! [Skotlex]
		return 0;

	sc = status_get_sc(src);

	if (sc != nullptr && sc->empty())
		sc = nullptr;

	if (!skill_db.find(skill_id))
		return 0;

	if( sd ) {
		if( skill_isNotOk(skill_id, *sd) || !skill_check_condition_castbegin(*sd, skill_id, skill_lv) )
			return 0;
		if (skill_id == MG_FIREWALL && !skill_pos_maxcount_check(src, skill_x, skill_y, skill_id, skill_lv, BL_PC, true))
			return 0; // Special check for Firewall only
	}

	if( (skill_id >= SC_MANHOLE && skill_id <= SC_FEINTBOMB) && map_getcell(src->m, skill_x, skill_y, CELL_CHKMAELSTROM) ) {
		if (sd)
			clif_skill_fail( *sd, skill_id );
		return 0;
	}

	if (!status_check_skilluse(src, nullptr, skill_id, 0))
		return 0;

	// Fail if the targetted skill is near NPC [Cydh]
	if(skill_get_inf2(skill_id, INF2_DISABLENEARNPC) && !ignore_range && skill_isNotOk_npcRange(src,skill_id,skill_lv,skill_x,skill_y)) {
		if (sd)
			clif_skill_fail( *sd, skill_id );

		return 0;
	}

	// Check range and obstacle
	bl.type = BL_NUL;
	bl.m = src->m;
	bl.x = skill_x;
	bl.y = skill_y;

	if (src->type == BL_NPC) // NPC-objects can override cast distance
		range = AREA_SIZE; // Maximum visible distance before NPC goes out of sight
	else
		range = skill_get_range2(src, skill_id, skill_lv, true); // Skill cast distance from database

	// New action request received, delete previous action request if not executed yet
	if(ud->stepaction || ud->steptimer != INVALID_TIMER)
		unit_stop_stepaction(src);
	// Remember the skill request from the client while walking to the next cell
	if(src->type == BL_PC && ud->walktimer != INVALID_TIMER && (!battle_check_range(src, &bl, range-1) || ignore_range)) {
		struct map_data *md = &map[src->m];
		// Convert coordinates to target_to so we can use it as target later
		ud->stepaction = true;
		ud->target_to = (skill_x + skill_y*md->xs);
		ud->stepskill_id = skill_id;
		ud->stepskill_lv = skill_lv;
		return 0; // Attacking will be handled by unit_walktoxy_timer in this case
	}

	if (!ignore_range) {
		if( skill_get_state(ud->skill_id) == ST_MOVE_ENABLE ) {
			if( !unit_can_reach_bl(src, &bl, range + 1, 1, nullptr, nullptr) )
				return 0; // Walk-path check failed.
		}else if( !battle_check_range(src, &bl, range) )
			return 0; // Arrow-path check failed.
	}
	unit_stop_attack(src);

	// Moved here to prevent Suffragium from ending if skill fails
#ifndef RENEWAL_CAST
	casttime = skill_castfix_sc(src, casttime, skill_get_castnodex(skill_id));
#else
	casttime = skill_vfcastfix(src, casttime, skill_id, skill_lv );
#endif

	ud->state.skillcastcancel = castcancel&&casttime>0?1:0;

// 	if( sd )
// 	{
// 		switch( skill_id )
// 		{
// 		case ????:
// 			sd->canequip_tick = tick + casttime;
// 		}
// 	}

	ud->skill_id    = skill_id;
	ud->skill_lv    = skill_lv;
	ud->skillx      = skill_x;
	ud->skilly      = skill_y;
	ud->skilltarget = 0;

	// Set attack and act delays
	// Please note that the call below relies on ud->skill_id being set!
	unit_set_attackdelay(*src, tick, DELAY_EVENT_CASTBEGIN_POS);
	// Apply cast time and general delays
	unit_set_castdelay(*ud, tick, (skill_get_cast(skill_id, skill_lv) != 0) ? casttime : 0);

	if( sc ) {
		// These 3 status do not stack, so it's efficient to use if-else
		if (sc->getSCE(SC_CLOAKING) && !(sc->getSCE(SC_CLOAKING)->val4&4)) {
			status_change_end(src, SC_CLOAKING);

			if (!src->prev)
				return 0; // Warped away!
		} else if (sc->getSCE(SC_CLOAKINGEXCEED) && !(sc->getSCE(SC_CLOAKINGEXCEED)->val4&4)) {
			status_change_end(src, SC_CLOAKINGEXCEED);

			if (!src->prev)
				return 0;
		} else if (sc->getSCE(SC_NEWMOON)) {
			status_change_end(src, SC_NEWMOON);

			if (!src->prev)
				return 0;
		}
	}

	unit_stop_walking( src, USW_FIXPOS );

	// SC_MAGICPOWER needs to switch states at start of cast
#ifndef RENEWAL
	skill_toggle_magicpower(src, skill_id);
#endif

	// In official this is triggered even if no cast time.
	clif_skillcasting(src, src->id, 0, skill_x, skill_y, skill_id, skill_lv, skill_get_ele(skill_id, skill_lv), casttime);

	if( casttime > 0 ) {
		ud->skilltimer = add_timer( tick+casttime, skill_castend_pos, src->id, 0 );

		if( (sd && pc_checkskill(sd,SA_FREECAST) > 0) || skill_id == LG_EXEEDBREAK)
			status_calc_bl(&sd->bl, { SCB_SPEED, SCB_ASPD });
	} else {
		ud->skilltimer = INVALID_TIMER;
		skill_castend_pos(ud->skilltimer,tick,src->id,0);
	}

	if( sd && battle_config.prevent_logout_trigger&PLT_SKILL )
		sd->canlog_tick = gettick();

	return 1;
}

/**
 * Update a unit's attack target
 * @param ud: Unit data
 * @param target_id: Target ID (bl->id)
 * @return 0
 */
int32 unit_set_target(struct unit_data* ud, int32 target_id)
{
	nullpo_ret(ud);

	if( ud->target != target_id ) {
		struct unit_data * ux;
		struct block_list* target;
	
		if (ud->target && (target = map_id2bl(ud->target)) && (ux = unit_bl2ud(target)) && ux->target_count > 0)
			ux->target_count--;

		if (target_id && (target = map_id2bl(target_id)) && (ux = unit_bl2ud(target)) && ux->target_count < 255)
			ux->target_count++;
	}

	ud->target = target_id;

	return 0;
}

/**
 * Helper function used in foreach calls to stop auto-attack timers
 * @param bl: Block object
 * @param ap: func* with va_list values
 *   Parameter: '0' - everyone, 'id' - only those attacking someone with that id
 * @return 1 on success or 0 otherwise
 */
int32 unit_stopattack(struct block_list *bl, va_list ap)
{
	struct unit_data *ud = unit_bl2ud(bl);
	int32 id = va_arg(ap, int32);

	if (ud && ud->attacktimer != INVALID_TIMER && (!id || id == ud->target)) {
		unit_stop_attack(bl);
		return 1;
	}

	return 0;
}

/**
 * Stop a unit's attacks
 * @param bl: Object to stop
 */
void unit_stop_attack(struct block_list *bl)
{
	struct unit_data *ud;
	nullpo_retv(bl);
	ud = unit_bl2ud(bl);
	nullpo_retv(ud);

	//Clear target
	unit_set_target(ud, 0);

	if(ud->attacktimer == INVALID_TIMER)
		return;

	//Clear timer
	delete_timer(ud->attacktimer, unit_attack_timer);
	ud->attacktimer = INVALID_TIMER;
}

/**
 * Stop a unit's step action
 * @param bl: Object to stop
 */
void unit_stop_stepaction(struct block_list *bl)
{
	struct unit_data *ud;
	nullpo_retv(bl);
	ud = unit_bl2ud(bl);
	nullpo_retv(ud);

	//Clear remembered step action
	ud->stepaction = false;
	ud->target_to = 0;
	ud->stepskill_id = 0;
	ud->stepskill_lv = 0;

	if(ud->steptimer == INVALID_TIMER)
		return;

	//Clear timer
	delete_timer(ud->steptimer, unit_step_timer);
	ud->steptimer = INVALID_TIMER;
}

/**
 * Removes a unit's target due to being unattackable
 * @param bl: Object to unlock target
 * @return 0
 */
int32 unit_unattackable(struct block_list *bl)
{
	struct unit_data *ud = unit_bl2ud(bl);

	if (ud) {
		ud->state.attack_continue = 0;
		ud->state.step_attack = 0;
		ud->target_to = 0;
		unit_set_target(ud, 0);
	}

	if(bl->type == BL_MOB)
		mob_unlocktarget((struct mob_data*)bl, gettick());
	else if(bl->type == BL_PET)
		pet_unlocktarget((struct pet_data*)bl);

	return 0;
}

/**
 * Requests a unit to attack a target
 * @param src: Object initiating attack
 * @param target_id: Target ID (bl->id)
 * @param continuous: 
 *		0x1 - Whether or not the attack is ongoing
 *		0x2 - Whether function was called from unit_step_timer or not
 * @return Success(0); Fail(1);
 */
int32 unit_attack(struct block_list *src,int32 target_id,int32 continuous)
{
	struct block_list *target;
	struct unit_data  *ud;
	int32 range;

	nullpo_ret(ud = unit_bl2ud(src));

	target = map_id2bl(target_id);
	if( target == nullptr || status_isdead(*target) ) {
		unit_unattackable(src);
		return 1;
	}

	if( src->type == BL_PC &&
		target->type == BL_NPC ) {
		// Monster npcs [Valaris]
		npc_click((TBL_PC*)src,(TBL_NPC*)target);
		return 0;
	}

	if( !unit_can_attack(src, target_id) ) {
		unit_stop_attack(src);
		return 0;
	}

	if( battle_check_target(src,target,BCT_ENEMY) <= 0 || !status_check_skilluse(src, target, 0, 0) ) {
		unit_unattackable(src);
		return 1;
	}

	ud->state.attack_continue = (continuous&1)?1:0;
	ud->state.step_attack = (continuous&2)?1:0;
	unit_set_target(ud, target_id);

	range = status_get_range(src);

	if (continuous) // If you're to attack continously, set to auto-chase character
		ud->chaserange = range;

	// Just change target/type. [Skotlex]
	if(ud->attacktimer != INVALID_TIMER)
		return 0;

	// New action request received, delete previous action request if not executed yet
	if(ud->stepaction || ud->steptimer != INVALID_TIMER)
		unit_stop_stepaction(src);
	// Remember the attack request from the client while walking to the next cell
	if(src->type == BL_PC && ud->walktimer != INVALID_TIMER && !battle_check_range(src, target, range-1)) {
		ud->stepaction = true;
		ud->target_to = ud->target;
		ud->stepskill_id = 0;
		ud->stepskill_lv = 0;
		return 0; // Attacking will be handled by unit_walktoxy_timer in this case
	}
	
	if(DIFF_TICK(ud->attackabletime, gettick()) > 0) // Do attack next time it is possible. [Skotlex]
		ud->attacktimer=add_timer(ud->attackabletime,unit_attack_timer,src->id,0);
	else // Attack NOW.
		unit_attack_timer(INVALID_TIMER, gettick(), src->id, 0);

	// Monster state is set regardless of whether the attack is executed now or later
	// The check is here because unit_attack can be called from both the monster AI and the walking logic
	if (src->type == BL_MOB) {
		mob_data& md = reinterpret_cast<mob_data&>(*src);
		mob_setstate(md, MSS_BERSERK);
	}

	return 0;
}

/** 
 * Cancels an ongoing combo, resets attackable time, and restarts the
 * attack timer to resume attack after amotion time
 * @author [Skotlex]
 * @param bl: Object to cancel combo
 * @return Success(1); Fail(0);
 */
int32 unit_cancel_combo(struct block_list *bl)
{
	struct unit_data  *ud;

	if (!status_change_end(bl, SC_COMBO))
		return 0; // Combo wasn't active.

	ud = unit_bl2ud(bl);
	nullpo_ret(ud);

	ud->attackabletime = gettick() + status_get_amotion(bl);

	if (ud->attacktimer == INVALID_TIMER)
		return 1; // Nothing more to do.

	delete_timer(ud->attacktimer, unit_attack_timer);
	ud->attacktimer=add_timer(ud->attackabletime,unit_attack_timer,bl->id,0);

	return 1;
}

/**
 * Does a path_search to check if a position can be reached
 * @param bl: Object to check path
 * @param x: X coordinate that will be path searched
 * @param y: Y coordinate that will be path searched
 * @param easy: Easy(1) or Hard(0) path check (hard attempts to go around obstacles)
 * @return true or false
 */
bool unit_can_reach_pos(struct block_list *bl,int32 x,int32 y, int32 easy)
{
	nullpo_retr(false, bl);

	if (bl->x == x && bl->y == y) // Same place
		return true;

	return path_search(nullptr,bl->m,bl->x,bl->y,x,y,easy,CELL_CHKNOREACH);
}

/**
 * Does a path_search to check if a unit can be reached
 * @param bl: Object to check path
 * @param tbl: Target to be checked for available path
 * @param range: The number of cells away from bl that the path should be checked
 * @param easy: Easy(1) or Hard(0) path check (hard attempts to go around obstacles)
 * @param x: Pointer storing a valid X coordinate around tbl that can be reached
 * @param y: Pointer storing a valid Y coordinate around tbl that can be reached
 * @return true or false
 */
bool unit_can_reach_bl(struct block_list *bl,struct block_list *tbl, int32 range, int32 easy, int16 *x, int16 *y)
{
	struct walkpath_data wpd;
	int16 dx, dy;

	nullpo_retr(false, bl);
	nullpo_retr(false, tbl);

	if( bl->m != tbl->m)
		return false;

	if( bl->x == tbl->x && bl->y == tbl->y )
		return true;

	if(range > 0 && !check_distance_bl(bl, tbl, range))
		return false;

	// It judges whether it can adjoin or not.
	dx = tbl->x - bl->x;
	dy = tbl->y - bl->y;
	dx = (dx > 0) ? 1 : ((dx < 0) ? -1 : 0);
	dy = (dy > 0) ? 1 : ((dy < 0) ? -1 : 0);

	if (map_getcell(tbl->m,tbl->x-dx,tbl->y-dy,CELL_CHKNOPASS)) { // Look for a suitable cell to place in.
		int32 i;

		for(i = 0; i < 8 && map_getcell(tbl->m,tbl->x-dirx[i],tbl->y-diry[i],CELL_CHKNOPASS); i++);

		if (i == 8)
			return false; // No valid cells.

		dx = dirx[i];
		dy = diry[i];
	}

	if (x)
		*x = tbl->x-dx;

	if (y)
		*y = tbl->y-dy;

	if (!path_search(&wpd,bl->m,bl->x,bl->y,tbl->x-dx,tbl->y-dy,easy,CELL_CHKNOREACH))
		return false;

#ifdef OFFICIAL_WALKPATH
	if( bl->type != BL_NPC // If type is a NPC, please disregard.
		&& wpd.path_len > 14 // Official number of walkable cells is 14 if and only if there is an obstacle between. [malufett]
		&& !path_search_long(nullptr, bl->m, bl->x, bl->y, tbl->x-dx, tbl->y-dy, CELL_CHKNOPASS) ) // Check if there is an obstacle between
			return false;
#endif

	return true;
}

/**
 * Calculates position of Pet/Mercenary/Homunculus/Elemental
 * @param bl: Object to calculate position
 * @param tx: X coordinate to go to
 * @param ty: Y coordinate to go to
 * @param dir: Direction which to be 2 cells from master's position
 * @return Success(0); Fail(1);
 */
int32 unit_calc_pos(struct block_list *bl, int32 tx, int32 ty, uint8 dir)
{
	int32 dx, dy, x, y;
	struct unit_data *ud = unit_bl2ud(bl);

	nullpo_ret(ud);

	if(dir >= DIR_MAX || dir <= DIR_CENTER)
		return 1;

	ud->to_x = tx;
	ud->to_y = ty;

	// 2 cells from Master Position
	dx = -dirx[dir] * 2;
	dy = -diry[dir] * 2;
	x = tx + dx;
	y = ty + dy;

	if( !unit_can_reach_pos(bl, x, y, 0) ) {
		if( dx > 0 )
			x--;
		else if( dx < 0 )
			x++;

		if( dy > 0 )
			y--;
		else if( dy < 0 )
			y++;

		if( !unit_can_reach_pos(bl, x, y, 0) ) {
			int32 i;

			for( i = 0; i < 12; i++ ) {
				int32 k = rnd_value<int32>(DIR_NORTH, DIR_NORTHEAST); // Pick a Random Dir

				dx = -dirx[k] * 2;
				dy = -diry[k] * 2;
				x = tx + dx;
				y = ty + dy;

				if( unit_can_reach_pos(bl, x, y, 0) )
					break;
				else {
					if( dx > 0 )
						x--;
					else if( dx < 0 )
						x++;

					if( dy > 0 )
						y--;
					else if( dy < 0 )
						y++;

					if( unit_can_reach_pos(bl, x, y, 0) )
						break;
				}
			}

			if( i == 12 ) {
				x = tx; y = tx; // Exactly Master Position

				if( !unit_can_reach_pos(bl, x, y, 0) )
					return 1;
			}
		}
	}

	ud->to_x = x;
	ud->to_y = y;

	return 0;
}

/**
 * Function timer to continuously attack
 * @param src: Object to continuously attack
 * @param tid: Timer ID
 * @param tick: Current tick
 * @return Attackable(1); Unattackable(0);
 */
static int32 unit_attack_timer_sub(struct block_list* src, int32 tid, t_tick tick)
{
	struct block_list *target;
	struct unit_data *ud;
	map_session_data *sd = nullptr;
	struct mob_data *md = nullptr;
	int32 range;

	if( (ud = unit_bl2ud(src)) == nullptr )
		return 0;

	if( ud->attacktimer != tid ) {
		ShowError("unit_attack_timer %d != %d\n",ud->attacktimer,tid);
		return 0;
	}

	sd = BL_CAST(BL_PC, src);
	md = BL_CAST(BL_MOB, src);

	// Make sure attacktimer is removed before doing anything else
	ud->attacktimer = INVALID_TIMER;

	// Note: Officially there is no such thing as an attack timer. All actions are driven by the client or the AI.
	// We use the continuous attack timers to have accurate attack timings that don't depend on the AI interval.
	// However, for a clean implementation we still should channel through the whole AI code so the same rules
	// apply as usual and we don't need to code extra rules. Currently we resolved this only for monsters.
	// We don't want this to trigger on direct calls of the timer function as that should just execute the attack.
	if (md != nullptr && tid != INVALID_TIMER)
		return mob_ai_sub_hard_attacktimer(*md, tick);

	target = map_id2bl(ud->target);

	if( src == nullptr || src->prev == nullptr || target==nullptr || target->prev == nullptr )
		return 0;

	if( status_isdead(*src) || status_isdead(*target) ||
			battle_check_target(src,target,BCT_ENEMY) <= 0 || !status_check_skilluse(src, target, 0, 0)
#ifdef OFFICIAL_WALKPATH
	   || !path_search_long(nullptr, src->m, src->x, src->y, target->x, target->y, CELL_CHKWALL)
#endif
	   || !unit_can_attack(src, target->id) )
		return 0; // Can't attack under these conditions

	if( ud->skilltimer != INVALID_TIMER && !(sd && pc_checkskill(sd,SA_FREECAST) > 0) )
		return 0; // Can't attack while casting

	if( !battle_config.sdelay_attack_enable && DIFF_TICK(ud->canact_tick,tick) > 0 && !(sd && pc_checkskill(sd,SA_FREECAST) > 0) ) {
		// Attacking when under cast delay has restrictions:
		if( tid == INVALID_TIMER ) { // Requested attack.
			if(sd)
				clif_skill_fail( *sd, 1, USESKILL_FAIL_SKILLINTERVAL );

			return 0;
		}

		// Otherwise, we are in a combo-attack, delay this until your canact time is over. [Skotlex]
		if( ud->state.attack_continue ) {
			if( DIFF_TICK(ud->canact_tick, ud->attackabletime) > 0 )
				ud->attackabletime = ud->canact_tick;

			ud->attacktimer=add_timer(ud->attackabletime,unit_attack_timer,src->id,0);
		}

		return 1;
	}

	status_data* sstatus = status_get_status_data(*src);
	range = sstatus->rhw.range;

	if( (unit_is_walking(target) || ud->state.step_attack)
		&& (target->type == BL_PC || !map_getcell(target->m,target->x,target->y,CELL_CHKICEWALL)) )
		range++; // Extra range when chasing (does not apply to mobs locked in an icewall)

	if(sd && !check_distance_client_bl(src,target,range)) {
		// Player tries to attack but target is too far, notify client
		clif_movetoattack( *sd, *target );
		return 1;
	} else if(md && !check_distance_bl(src,target,range)) {
		// Monster: Chase if required
		unit_walktobl(src,target,ud->chaserange,ud->state.walk_easy|2);
		return 1;
	}

	if( !battle_check_range(src,target,range) ) {
		// Within range, but no direct line of attack
		// This code can usually only be reached if OFFICIAL_WALKPATH is disabled
		if (ud->state.attack_continue && ud->chaserange > 1) {
			ud->chaserange = std::max(1, ud->chaserange - 2);

			// Walk closer / around the obstacle and start attacking once you are in range
			return unit_walktobl(src,target,ud->chaserange,ud->state.walk_easy|2);
		}
		// Can't attack even though next to the target? Giving up here.
		return 0;
	}

	// Sync packet only for players.
	// Non-players use the sync packet on the walk timer. [Skotlex]
	if (tid == INVALID_TIMER && sd)
		clif_fixpos( *src );

	if( DIFF_TICK(ud->attackabletime,tick) <= 0 ) {
		if (battle_config.attack_direction_change && (src->type&battle_config.attack_direction_change))
			unit_setdir(src, map_calc_dir(src, target->x, target->y), false);

		if(ud->walktimer != INVALID_TIMER)
			unit_stop_walking( src, USW_FIXPOS );

		if(md) {
			if (status_has_mode(sstatus,MD_ASSIST) && DIFF_TICK(tick, md->last_linktime) >= MIN_MOBLINKTIME) { 
				// Link monsters nearby [Skotlex]
				md->last_linktime = tick;
				map_foreachinshootrange(mob_linksearch, src, battle_config.assist_range, BL_MOB, md->mob_id, target->id, tick);
			}
		}

		if(src->type == BL_PET && pet_attackskill((TBL_PET*)src, target->id))
			return 1;

		map_freeblock_lock();
		ud->attacktarget_lv = battle_weapon_attack(src,target,tick,0);

		if(sd && sd->status.pet_id > 0 && sd->pd && battle_config.pet_attack_support)
			pet_target_check(sd->pd,target,0);

		map_freeblock_unlock();

		/**
		 * Applied when you're unable to attack (e.g. out of ammo)
		 * We should stop here otherwise timer keeps on and this happens endlessly
		 */
		if( ud->attacktarget_lv == ATK_NONE )
			return 1;

		unit_set_attackdelay(*src, tick, DELAY_EVENT_ATTACK);

		// Only reset skill_id here if no skilltimer is currently ongoing
		if (ud->skilltimer == INVALID_TIMER)
			ud->skill_id = 0;

		// You can't move during your attack motion
		if (src->type&battle_config.attack_walk_delay)
			unit_set_walkdelay(src, tick, sstatus->amotion, 1);
	}

	if(ud->state.attack_continue) {
		if (src->type == BL_PC && battle_config.idletime_option&IDLE_ATTACK)
			((TBL_PC*)src)->idletime = last_tick;

		ud->attacktimer = add_timer(ud->attackabletime,unit_attack_timer,src->id,0);
	}

	if( sd && battle_config.prevent_logout_trigger&PLT_ATTACK )
		sd->canlog_tick = gettick();

	return 1;
}

/**
 * Timer function to cancel attacking if unit has become unattackable
 * @param tid: Timer ID
 * @param tick: Current tick
 * @param id: Object to cancel attack if applicable
 * @param data: Data passed from timer call
 * @return 0
 */
static TIMER_FUNC(unit_attack_timer){
	struct block_list *bl;

	bl = map_id2bl(id);

	if (bl != nullptr) {
		// Execute attack
		if (unit_attack_timer_sub(bl, tid, tick) == 0)
			unit_unattackable(bl);
	}

	return 0;
}

/**
 * Determines whether a player can attack based on status changes
 *  Why not use status_check_skilluse?
 *  "src MAY be null to indicate we shouldn't check it, this is a ground-based skill attack."
 *  Even ground-based attacks should be blocked by these statuses
 * Called from unit_attack and unit_attack_timer_sub
 * @retval true Can attack
 **/
bool unit_can_attack(struct block_list *bl, int32 target_id) {
	nullpo_retr(false, bl);

	if (bl->type == BL_PC) {
		map_session_data *sd = ((TBL_PC *)bl);

		if (sd && ((sd->state.block_action & PCBLOCK_ATTACK) || pc_isridingwug(sd)))
			return false;
	}

	status_change *sc;

	if (!(sc = status_get_sc(bl)))
		return true;

	if (sc->cant.attack || (sc->getSCE(SC_VOICEOFSIREN) && sc->getSCE(SC_VOICEOFSIREN)->val2 == target_id))
		return false;

	return true;
}

/**
 * Cancels a skill's cast
 * @param bl: Object to cancel cast
 * @param type: Cancel check flag
 *	&1: Cancel skill stored in sd->skill_id_old instead
 *	&2: Cancel only if skill is cancellable
 * @return Success(1); Fail(0);
 */
int32 unit_skillcastcancel(struct block_list *bl, char type)
{
	map_session_data *sd = nullptr;
	struct unit_data *ud = unit_bl2ud( bl);
	t_tick tick = gettick();
	int32 ret = 0, skill_id;

	nullpo_ret(bl);

	if (!ud || ud->skilltimer == INVALID_TIMER)
		return 0; // Nothing to cancel.

	sd = BL_CAST(BL_PC, bl);

	if (type&2) { // See if it can be cancelled.
		if (!ud->state.skillcastcancel)
			return 0;

		if (sd && (sd->special_state.no_castcancel2 ||
			((sd->sc.getSCE(SC_UNLIMITEDHUMMINGVOICE) || sd->special_state.no_castcancel) && !map_flag_gvg2(bl->m) && !map_getmapflag(bl->m, MF_BATTLEGROUND)))) // fixed flags being read the wrong way around [blackhole89]
			return 0;
	}

	ud->canact_tick = tick;

	if(type&1 && sd)
		skill_id = sd->skill_id_old;
	else
		skill_id = ud->skill_id;

	if (skill_get_inf(skill_id) & INF_GROUND_SKILL)
		ret=delete_timer( ud->skilltimer, skill_castend_pos );
	else
		ret=delete_timer( ud->skilltimer, skill_castend_id );

	if(ret < 0)
		ShowError("delete timer error : skill_id : %d\n",ret);

	ud->skilltimer = INVALID_TIMER;

	if( sd && (pc_checkskill(sd,SA_FREECAST) > 0 || skill_id == LG_EXEEDBREAK) )
		status_calc_bl(&sd->bl, { SCB_SPEED, SCB_ASPD });

	if( sd ) {
		switch( skill_id ) {
			case CG_ARROWVULCAN:
				sd->canequip_tick = tick;
				break;
		}
	}

	unit_set_attackdelay(*bl, tick, DELAY_EVENT_CASTCANCEL);

	if (bl->type == BL_MOB) {
		mob_data& md = reinterpret_cast<mob_data&>(*bl);
		md.skill_idx = -1;
	}

	clif_skillcastcancel( *bl );

	return 1;
}

/**
 * Initialized data on a unit
 * @param bl: Object to initialize data on
 */
void unit_dataset(struct block_list *bl)
{
	struct unit_data *ud;

	nullpo_retv(ud = unit_bl2ud(bl));

	memset( ud, 0, sizeof( struct unit_data) );
	ud->bl             = bl;
	ud->walktimer      = INVALID_TIMER;
	ud->skilltimer     = INVALID_TIMER;
	ud->attacktimer    = INVALID_TIMER;
	ud->steptimer      = INVALID_TIMER;
	t_tick tick = gettick();
	ud->attackabletime = tick;
	ud->canact_tick = tick;
	ud->canmove_tick = tick;
	ud->endure_tick = tick;
	ud->dmg_tick = 0;
	ud->sx = 8;
	ud->sy = 8;
}

/**
 * Returns the remaining max amount of skill units per object for a specific skill
 * @param ud: Unit data
 * @param skill_id: Skill to search for
 * @param maxcount: Maximum amount of placeable units
 */
void unit_skillunit_maxcount(unit_data& ud, uint16 skill_id, int& maxcount) {
	for (const auto su : ud.skillunits) {
		if (su->skill_id == skill_id && --maxcount == 0 )
			break;
	}
}

/**
 * Gets the number of units attacking another unit
 * @param bl: Object to check amount of targets
 * @return number of targets or 0
 */
int32 unit_counttargeted(struct block_list* bl)
{
	struct unit_data* ud;

	if( bl && (ud = unit_bl2ud(bl)) )
		return ud->target_count;

	return 0;
}

/**
 * Makes 'bl' that attacking 'src' switch to attack 'target'
 * @param bl
 * @param ap
 * @param src Current target
 * @param target New target
 **/
int32 unit_changetarget(block_list *bl, va_list ap) {
	if (bl == nullptr)
		return 1;
	unit_data *ud = unit_bl2ud(bl);
	block_list *src = va_arg(ap, block_list *);
	block_list *target = va_arg(ap, block_list *);

	if (ud == nullptr || src == nullptr || target == nullptr || ud->target == target->id)
		return 1;
	if (ud->target <= 0 && ud->target_to <= 0)
		return 1;
	if (ud->target != src->id && ud->target_to != src->id)
		return 1;

	unit_changetarget_sub(*ud, *target);

	//unit_attack(bl, target->id, ud->state.attack_continue);
	return 0;
}

/**
 * Changes the target of a unit
 * @param ud: Unit data
 * @param target: New target data
 **/
void unit_changetarget_sub(unit_data& ud, block_list& target) {
	if (status_isdead(target))
		return;

	if (ud.bl->type == BL_MOB)
		reinterpret_cast<mob_data*>(ud.bl)->target_id = target.id;
	if (ud.target_to > 0)
		ud.target_to = target.id;
	if (ud.skilltarget > 0)
		ud.skilltarget = target.id;
	unit_set_target(&ud, target.id);
}

/**
 * Removes a bl/ud from the map
 * On kill specifics are not performed here, check status_damage()
 * @param bl: Object to remove from map
 * @param clrtype: How bl is being removed
 *	0: Assume bl is being warped
 *	1: Death, appropriate cleanup performed
 * @param file, line, func: Call information for debug purposes
 * @return Success(1); Couldn't be removed or bl was free'd(0)
 */
int32 unit_remove_map_(struct block_list *bl, clr_type clrtype, const char* file, int32 line, const char* func)
{
	struct unit_data *ud = unit_bl2ud(bl);
	status_change *sc = status_get_sc(bl);

	nullpo_ret(ud);

	if(bl->prev == nullptr)
		return 0; // Already removed?

	map_freeblock_lock();

	if (ud->walktimer != INVALID_TIMER)
		unit_stop_walking(bl,USW_RELEASE_TARGET);

	if (clrtype == CLR_DEAD)
		ud->state.blockedmove = true;

	if (ud->skilltimer != INVALID_TIMER)
		unit_skillcastcancel(bl,0);

	//Clear target even if there is no timer
	if (ud->target || ud->attacktimer != INVALID_TIMER)
		unit_stop_attack(bl);

	//Clear stepaction even if there is no timer
	if (ud->stepaction || ud->steptimer != INVALID_TIMER)
		unit_stop_stepaction(bl);

	// Do not reset can-act delay. [Skotlex]
	ud->attackabletime = ud->canmove_tick /*= ud->canact_tick*/ = gettick();

	if(sc != nullptr && !sc->empty() ) { // map-change/warp dispells.
		status_db.removeByStatusFlag(bl, { SCF_REMOVEONCHANGEMAP });

		// Ensure the bl is a PC; if so, we'll handle the removal of cloaking and cloaking exceed later
		if ( bl->type != BL_PC ) {
			status_change_end(bl, SC_CLOAKING);
			status_change_end(bl, SC_CLOAKINGEXCEED);
		}
		if (sc->getSCE(SC_GOSPEL) && sc->getSCE(SC_GOSPEL)->val4 == BCT_SELF)
			status_change_end(bl, SC_GOSPEL);
		if (sc->getSCE(SC_PROVOKE) && sc->getSCE(SC_PROVOKE)->val4 == 1)
			status_change_end(bl, SC_PROVOKE); //End infinite provoke to prevent exploit
	}

	switch( bl->type ) {
		case BL_PC: {
			map_session_data *sd = (map_session_data*)bl;

			if(sd->shadowform_id) { // If shadow target has leave the map
			    struct block_list *d_bl = map_id2bl(sd->shadowform_id);

			    if( d_bl )
				    status_change_end(d_bl,SC__SHADOWFORM);
			}

			// Leave/reject all invitations.
			if(sd->chatID)
				chat_leavechat(sd,0);

			if(sd->trade_partner.id > 0)
				trade_tradecancel(sd);

			searchstore_close(*sd);

			if (sd->menuskill_id != AL_TELEPORT) { //bugreport:8027
				if (sd->state.storage_flag == 1)
					storage_storage_quit(sd,0);
				else if (sd->state.storage_flag == 2)
					storage_guild_storage_quit(sd, 0);
				else if (sd->state.storage_flag == 3)
					storage_premiumStorage_quit(sd);

				sd->state.storage_flag = 0; //Force close it when being warped.
			}

			if(sd->party_invite > 0)
				party_reply_invite( *sd, sd->party_invite, 0 );

			if(sd->guild_invite > 0)
				guild_reply_invite( *sd, sd->guild_invite, 0 );

			if(sd->guild_alliance > 0)
				guild_reply_reqalliance(sd,sd->guild_alliance_account,0);

			if(sd->menuskill_id)
				sd->menuskill_id = sd->menuskill_val = 0;

			if( !sd->npc_ontouch_.empty() )
				npc_touchnext_areanpc(sd,true);

			// Check if warping and not changing the map.
			if ( sd->state.warping && !sd->state.changemap ) {
				status_change_end(bl, SC_CLOAKING);
				status_change_end(bl, SC_CLOAKINGEXCEED);
			}

			sd->npc_shopid = 0;
			sd->adopt_invite = 0;

			if(sd->pvp_timer != INVALID_TIMER) {
				delete_timer(sd->pvp_timer,pc_calc_pvprank_timer);
				sd->pvp_timer = INVALID_TIMER;
				sd->pvp_rank = 0;
			}

			if(sd->duel_group > 0)
				duel_leave(sd->duel_group, sd);

			if(pc_issit(sd) && pc_setstand(sd, false))
				skill_sit(sd, false);

			party_send_dot_remove(sd);// minimap dot fix [Kevin]
			guild_send_dot_remove(sd);
			bg_send_dot_remove(sd);

			if( map[bl->m].users <= 0 || sd->state.debug_remove_map ) {
				// This is only place where map users is decreased, if the mobs were removed
				// too soon then this function was executed too many times [FlavioJS]
				if( sd->debug_file == nullptr || !(sd->state.debug_remove_map) ) {
					sd->debug_file = "";
					sd->debug_line = 0;
					sd->debug_func = "";
				}

				ShowDebug("unit_remove_map: unexpected state when removing player AID/CID:%d/%d"
					" (active=%d connect_new=%d rewarp=%d changemap=%d debug_remove_map=%d)"
					" from map=%s (users=%d)."
					" Previous call from %s:%d(%s), current call from %s:%d(%s)."
					" Please report this!!!\n",
					sd->status.account_id, sd->status.char_id,
					sd->state.active, sd->state.connect_new, sd->state.rewarp, sd->state.changemap, sd->state.debug_remove_map,
					map[bl->m].name, map[bl->m].users,
					sd->debug_file, sd->debug_line, sd->debug_func, file, line, func);
			}
			else if (--map[bl->m].users == 0 && battle_config.dynamic_mobs)
				map_removemobs(bl->m);

			if( !pc_isinvisible(sd) ) // Decrement the number of active pvp players on the map
				--map[bl->m].users_pvp;

			if( sd->state.hpmeter_visible ) {
				map[bl->m].hpmeter_visible--;
				sd->state.hpmeter_visible = 0;
			}

			sd->state.debug_remove_map = 1; // Temporary state to track double remove_map's [FlavioJS]
			sd->debug_file = file;
			sd->debug_line = line;
			sd->debug_func = func;
			break;
		}
		case BL_MOB: {
			struct mob_data *md = (struct mob_data*)bl;

			// Drop previous target mob_slave_keep_target: no.
			if (!battle_config.mob_slave_keep_target)
				md->target_id=0;

			// When a monster is removed from map, its spotted log is cleared
			for (int32 i = 0; i < DAMAGELOG_SIZE; i++)
				md->spotted_log[i] = 0;

			md->attacked_id=0;
			mob_setstate(*md, MSS_IDLE);
			break;
		}
		case BL_PET: {
			struct pet_data *pd = (struct pet_data*)bl;

			if( pd->pet.intimate <= PET_INTIMATE_NONE && !(pd->master && !pd->master->state.active) ) {
				// If logging out, this is deleted on unit_free
				clif_clearunit_area( *bl, clrtype );
				map_delblock(bl);
				unit_free(bl,CLR_OUTSIGHT);
				map_freeblock_unlock();

				return 0;
			}
			break;
		}
		case BL_HOM: {
			struct homun_data *hd = (struct homun_data *)bl;

			ud->canact_tick = ud->canmove_tick; // It appears HOM do reset the can-act tick.

			if( !hd->homunculus.intimacy && !(hd->master && !hd->master->state.active) ) {
				// If logging out, this is deleted on unit_free
				clif_clearunit_area( *bl, clrtype );
				map_delblock(bl);
				unit_free(bl,CLR_OUTSIGHT);
				map_freeblock_unlock();

				return 0;
			}
			break;
		}
		case BL_MER: {
			s_mercenary_data *md = (s_mercenary_data *)bl;

			ud->canact_tick = ud->canmove_tick;

			if( mercenary_get_lifetime(md) <= 0 && !(md->master && !md->master->state.active) ) {
				clif_clearunit_area( *bl, clrtype );
				map_delblock(bl);
				unit_free(bl,CLR_OUTSIGHT);
				map_freeblock_unlock();

				return 0;
			}
			break;
		}
		case BL_ELEM: {
			s_elemental_data *ed = (s_elemental_data *)bl;

			ud->canact_tick = ud->canmove_tick;

			if( elemental_get_lifetime(ed) <= 0 && !(ed->master && !ed->master->state.active) ) {
				clif_clearunit_area( *bl, clrtype );
				map_delblock(bl);
				unit_free(bl,CLR_OUTSIGHT);
				map_freeblock_unlock();

				return 0;
			}
			break;
		}
		case BL_NPC:
			if (npc_remove_map( (TBL_NPC*)bl ) != 0)
				return 0;
			break;
		default:
			break;// do nothing
	}

	if (bl->type&(BL_CHAR|BL_PET)) {
		skill_unit_move(bl,gettick(),4);
		skill_cleartimerskill(bl);
	}

	switch (bl->type) {
		case BL_NPC:
			// already handled by npc_remove_map
			break;
		case BL_MOB:
			// /BL_MOB is handled by mob_dead unless the monster is not dead.
			if (status_isdead(*bl)) {
				map_delblock(bl);
				break;
			}
			[[fallthrough]];
		default:
			clif_clearunit_area( *bl, clrtype );
			map_delblock(bl);
			break;
	}

	map_freeblock_unlock();

	return 1;
}

/**
 * Refresh the area with a change in display of a unit.
 * @bl: Object to update
 */
void unit_refresh(struct block_list *bl, bool walking) {
	nullpo_retv(bl);

	if (bl->m < 0)
		return;

	struct map_data *mapdata = map_getmapdata(bl->m);

	// Using CLR_TRICKDEAD because other flags show effects
	// Probably need to use another flag or other way to refresh it
	if (mapdata->users) {
		clif_clearunit_area( *bl, CLR_TRICKDEAD ); // Fade out
		clif_spawn(bl,walking); // Fade in
	}
}

/**
 * Removes units of a master when the master is removed from map
 * @param sd: Player
 * @param clrtype: How bl is being removed
 *	0: Assume bl is being warped
 *	1: Death, appropriate cleanup performed
 */
void unit_remove_map_pc(map_session_data *sd, clr_type clrtype)
{
	unit_remove_map(&sd->bl,clrtype);

	//CLR_RESPAWN is the warp from logging out, CLR_TELEPORT is the warp from teleporting, but pets/homunc need to just 'vanish' instead of showing the warping animation.
	if (clrtype == CLR_RESPAWN || clrtype == CLR_TELEPORT)
		clrtype = CLR_OUTSIGHT;

	if(sd->pd)
		unit_remove_map(&sd->pd->bl, clrtype);

	if(hom_is_active(sd->hd))
		unit_remove_map(&sd->hd->bl, clrtype);

	if(sd->md)
		unit_remove_map(&sd->md->bl, clrtype);

	if(sd->ed)
		unit_remove_map(&sd->ed->bl, clrtype);
}

/**
 * Frees units of a player when is removed from map
 * Also free his pets/homon/mercenary/elemental/etc if he have any
 * @param sd: Player
 */
void unit_free_pc(map_session_data *sd)
{
	if (sd->pd)
		unit_free(&sd->pd->bl,CLR_OUTSIGHT);

	if (sd->hd)
		unit_free(&sd->hd->bl,CLR_OUTSIGHT);

	if (sd->md)
		unit_free(&sd->md->bl,CLR_OUTSIGHT);

	if (sd->ed)
		unit_free(&sd->ed->bl,CLR_OUTSIGHT);

	unit_free(&sd->bl,CLR_TELEPORT);
}

/**
 * Frees all related resources to the unit
 * @param bl: Object being removed from map
 * @param clrtype: How bl is being removed
 *	0: Assume bl is being warped
 *	1: Death, appropriate cleanup performed
 * @return 0
 */
int32 unit_free(struct block_list *bl, clr_type clrtype)
{
	struct unit_data *ud = unit_bl2ud( bl );

	nullpo_ret(ud);

	map_freeblock_lock();

	if( bl->prev )	// Players are supposed to logout with a "warp" effect.
		unit_remove_map(bl, clrtype);

	switch( bl->type ) {
		case BL_PC: {
			map_session_data *sd = (map_session_data*)bl;
			int32 i;

			if( status_isdead(*bl) )
				pc_setrestartvalue(sd,2);

			pc_delinvincibletimer(sd);

			pc_delautobonus(*sd, sd->autobonus, false);
			pc_delautobonus(*sd, sd->autobonus2, false);
			pc_delautobonus(*sd, sd->autobonus3, false);

			if( sd->followtimer != INVALID_TIMER )
				pc_stop_following(sd);

			if( sd->duel_invite > 0 )
				duel_reject(sd->duel_invite, sd);

			channel_pcquit(sd,0xF); // Leave all chan
			skill_blockpc_clear(*sd); // Clear all skill cooldown related

			// Notify friends that this char logged out.
			if( battle_config.friend_auto_add ){
				for( const s_friend& my_friend : sd->status.friends ){
					// Cancel early
					if( my_friend.char_id == 0 ){
						break;
					}

					if( map_session_data* tsd = map_charid2sd( my_friend.char_id ); tsd != nullptr ){
						for( const s_friend& their_friend : tsd->status.friends ){
							// Cancel early
							if( their_friend.char_id == 0 ){
								break;
							}

							if( their_friend.account_id != sd->status.account_id ){
								continue;
							}

							if( their_friend.char_id != sd->status.char_id ){
								continue;
							}

							clif_friendslist_toggle( *tsd, their_friend, false );
							break;
						}
					}
				}
			}else{
				map_foreachpc( clif_friendslist_toggle_sub, sd->status.account_id, sd->status.char_id, static_cast<int32>( false ) );
			}
			party_send_logout(sd);
			guild_send_memberinfoshort(sd,0);
			pc_cleareventtimer(sd);
			pc_inventory_rental_clear(sd);
			pc_delspiritball(sd, sd->spiritball, 1);
			pc_delspiritcharm(sd, sd->spiritcharm, sd->spiritcharm_type);
			mob_removeslaves(&sd->bl);

			if( sd->st && sd->st->state != RUN ) {// free attached scripts that are waiting
				script_free_state(sd->st);
				sd->st = nullptr;
				sd->npc_id = 0;
			}

			if( !sd->npc_id_dynamic.empty() ){
				for (const auto &it : sd->npc_id_dynamic) {
					struct npc_data* nd = map_id2nd( it );

					if( nd != nullptr ){
						// Erase the owner first to prevent loops from npc_unload
						nd->dynamicnpc.owner_char_id = 0;

						// Delete the NPC
						npc_unload( nd, true );
					}
				}
				// Update NPC event database
				npc_read_event_script();

				sd->npc_id_dynamic.clear();
			}

			sd->combos.clear();

			if( sd->sc_display_count ) { /* [Ind] */
				for( i = 0; i < sd->sc_display_count; i++ )
					ers_free(pc_sc_display_ers, sd->sc_display[i]);

				sd->sc_display_count = 0;
				aFree(sd->sc_display);
				sd->sc_display = nullptr;
			}

			if( sd->quest_log != nullptr ) {
				aFree(sd->quest_log);
				sd->quest_log = nullptr;
				sd->num_quests = sd->avail_quests = 0;
			}

			sd->qi_display.clear();

#if PACKETVER_MAIN_NUM >= 20150507 || PACKETVER_RE_NUM >= 20150429 || defined(PACKETVER_ZERO)
			sd->hatEffects.clear();
#endif

			if (sd->achievement_data.achievements)
				achievement_free(sd);

			// Clearing...
			if (sd->bonus_script.head)
				pc_bonus_script_clear(sd, BSF_REM_ALL);

			skill_clear_unitgroup(bl);
			status_change_clear(bl,1);
			break;
		}
		case BL_PET: {
			struct pet_data *pd = (struct pet_data*)bl;
			map_session_data *sd = pd->master;

			pet_delautobonus(*sd, pd->autobonus, false);
			pet_delautobonus(*sd, pd->autobonus2, false);
			pet_delautobonus(*sd, pd->autobonus3, false);

			pet_hungry_timer_delete(pd);
			pet_clear_support_bonuses(sd);

			if( pd->pet.intimate > PET_INTIMATE_NONE )
				intif_save_petdata(pd->pet.account_id,&pd->pet);
			else { // Remove pet.
				intif_delete_petdata(pd->pet.pet_id);

				if (sd)
					sd->status.pet_id = 0;
			}

			if( sd )
				sd->pd = nullptr;
			pd->master = nullptr;

			skill_clear_unitgroup(bl);
			status_change_clear(bl,1);
			break;
		}
		case BL_MOB: {
			struct mob_data *md = (struct mob_data*)bl;

			mob_free_dynamic_viewdata( md );

			if( md->spawn_timer != INVALID_TIMER ) {
				delete_timer(md->spawn_timer,mob_delayspawn);
				md->spawn_timer = INVALID_TIMER;
			}

			if( md->deletetimer != INVALID_TIMER ) {
				delete_timer(md->deletetimer,mob_timer_delete);
				md->deletetimer = INVALID_TIMER;
			}

			if (md->lootitems) {
				aFree(md->lootitems);
				md->lootitems = nullptr;
			}

			if( md->guardian_data ) {
				std::shared_ptr<guild_castle> gc = md->guardian_data->castle;

				if( md->guardian_data->number >= 0 && md->guardian_data->number < MAX_GUARDIANS )
					gc->guardian[md->guardian_data->number].id = 0;
				else {
					int32 i;

					ARR_FIND(0, gc->temp_guardians_max, i, gc->temp_guardians[i] == md->bl.id);
					if( i < gc->temp_guardians_max )
						gc->temp_guardians[i] = 0;
				}

				md->guardian_data->~guardian_data();
				aFree(md->guardian_data);
				md->guardian_data = nullptr;
			}

			if( md->spawn ) {
				md->spawn->active--;

				if( !md->spawn->state.dynamic ) { // Permanently remove the mob
					if( --md->spawn->num == 0 ) { // Last freed mob is responsible for deallocating the group's spawn data.
						aFree(md->spawn);
						md->spawn = nullptr;
					}
				}
			}

			if( md->base_status) {
				aFree(md->base_status);
				md->base_status = nullptr;
			}

			skill_clear_unitgroup(bl);
			status_change_clear(bl,1);

			if( mob_is_clone(md->mob_id) )
				mob_clone_delete(md);

			if( md->tomb_nid )
				mvptomb_destroy(md);
			break;
		}
		case BL_HOM:
		{
			struct homun_data *hd = (TBL_HOM*)bl;
			map_session_data *sd = hd->master;

			hom_hungry_timer_delete(hd);

			if( hd->homunculus.intimacy > 0 )
				hom_save(hd);
			else {
				intif_homunculus_requestdelete(hd->homunculus.hom_id);

				if( sd )
					sd->status.hom_id = 0;

#ifdef RENEWAL
				status_change_end(&sd->bl, SC_HOMUN_TIME);
#endif
			}

			skill_blockhomun_clear(*hd); // Clear all skill cooldown related

			if( sd )
				sd->hd = nullptr;
			hd->master = nullptr;

			skill_clear_unitgroup(bl);
			status_change_clear(bl,1);
			break;
		}
		case BL_MER: {
			s_mercenary_data *md = (TBL_MER*)bl;
			map_session_data *sd = md->master;

			if( mercenary_get_lifetime(md) > 0 )
				mercenary_save(md);
			else {
				intif_mercenary_delete(md->mercenary.mercenary_id);

				if( sd )
					sd->status.mer_id = 0;
			}

			if( sd )
				sd->md = nullptr;

			skill_blockmerc_clear(*md); // Clear all skill cooldown related
			mercenary_contract_stop(md);
			md->master = nullptr;

			skill_clear_unitgroup(bl);
			status_change_clear(bl,1);
			break;
		}
		case BL_ELEM: {
			s_elemental_data *ed = (TBL_ELEM*)bl;
			map_session_data *sd = ed->master;

			if( elemental_get_lifetime(ed) > 0 )
				elemental_save(ed);
			else {
				intif_elemental_delete(ed->elemental.elemental_id);

				if( sd )
					sd->status.ele_id = 0;
			}

			if( sd )
				sd->ed = nullptr;

			elemental_summon_stop(ed);
			ed->master = nullptr;

			skill_clear_unitgroup(bl);
			status_change_clear(bl,1);
			break;
		}
	}

	map_deliddb(bl);

	if( bl->type != BL_PC ) // Players are handled by map_quit
		map_freeblock(bl);

	map_freeblock_unlock();

	return 0;
}

static TIMER_FUNC(unit_shadowscar_timer) {
	block_list *bl = map_id2bl(id);

	if (bl == nullptr)
		return 1;

	unit_data *ud = unit_bl2ud(bl);

	if (ud == nullptr)
		return 1;

	std::vector<int32>::iterator it = ud->shadow_scar_timer.begin();

	while (it != ud->shadow_scar_timer.end()) {
		if (*it == tid) {
			ud->shadow_scar_timer.erase(it);
			break;
		}

		it++;
	}

	if (ud->shadow_scar_timer.empty())
		status_change_end( bl, SC_SHADOW_SCAR );

	return 0;
}

/**
 * Adds a Shadow Scar to unit for 'interval' ms.
 * @param ud: Unit data
 * @param interval: Duration
 */
void unit_addshadowscar(unit_data &ud, int32 interval) {
	if (ud.shadow_scar_timer.size() >= MAX_SHADOW_SCAR) {
		ShowWarning("unit_addshadowscar: Unit %s (%d) has reached the maximum amount of Shadow Scars (%d).\n", status_get_name(*ud.bl), ud.bl->id, MAX_SHADOW_SCAR);
		return;
	}

	ud.shadow_scar_timer.push_back(add_timer(gettick() + interval, unit_shadowscar_timer, ud.bl->id, 0));

	status_change *sc = status_get_sc(ud.bl);

	if (sc != nullptr) {
		if (sc->getSCE(SC_SHADOW_SCAR) != nullptr) {
			sc->getSCE(SC_SHADOW_SCAR)->val1 = static_cast<int32>(ud.shadow_scar_timer.size());
		} else {
			sc_start(ud.bl, ud.bl, SC_SHADOW_SCAR, 100, 1, INFINITE_TICK);
		}

		clif_enchantingshadow_spirit(ud);
	}
}

/**
 * Initialization function for unit on map start
 * called in map::do_init
 */
void do_init_unit(void){
	add_timer_func_list(unit_attack_timer,  "unit_attack_timer");
	add_timer_func_list(unit_walktoxy_timer,"unit_walktoxy_timer");
	add_timer_func_list(unit_walktobl_sub, "unit_walktobl_sub");
	add_timer_func_list(unit_delay_walktoxy_timer,"unit_delay_walktoxy_timer");
	add_timer_func_list(unit_delay_walktobl_timer,"unit_delay_walktobl_timer");
	add_timer_func_list(unit_teleport_timer,"unit_teleport_timer");
	add_timer_func_list(unit_step_timer,"unit_step_timer");
	add_timer_func_list(unit_shadowscar_timer, "unit_shadowscar_timer");
}

/**
 * Unit module destructor, (thing to do before closing the module)
 * called in map::do_final
 * @return 0
 */
void do_final_unit(void){
	// Nothing to do
}
