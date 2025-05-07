/*
	Lock system template model for Assignment 2 of 2IX20 - Software Specification.
	Set up for one lock and a configurable number of ships.

	This file contains:


	- process types for locks and ships that can be used as-is for the single lock case
	- a dummy specification of the main controller
	- initialization for the single-lock, single-ship case.
*/


// The number of locks.
#define N   3
// The number of ships.
#define M   4
// The maximum number of ships immediately at either side of a lock.
#define MAX 2

// LTL formulas to be verified
// Formula p1 holds if the first ship can always eventually enter the lock when going from west to east.
//ltl p1 { []<> (ship_status[0] == go_west_to_east_in_lock) }

// // When a request is made to open the western doors of lock i, eventually the western doors of lock i are open.
//ltl e1{[] (request_west[N-1]?[true] -> <> (doors_status[N-1].west == open))} 
 
// // When a request is made to open the eastern doors of lock i, eventually theeastern doors of lock i are open.
//ltl e2 {[] (request_east[N-1]?[true] -> (<> doors_status[N-1].east == open))}

// Always eventually a request is made to open the western doors of lock 0.
//ltl f1 {[]<> (request_west[0])}
//Always eventually a request is made to open the eastern doors of lock N −1.
//ltl f2 {[]<> (request_east[N-1])}


// Type for direction of ship.
mtype:direction = { go_west_to_east, go_west_to_east_in_lock, go_east_to_west, go_east_to_west_in_lock, goal_reached };

// Type for orientation of lock: side of lock with low water level
mtype:lock_orientation = { west_low, east_low };

// Type for water level.
mtype:level = { low_level, high_level };

// Type for lock side indication.
mtype:side = { west_side, east_side };

// Type for valve side indication.
mtype:valve_side = { low_side, high_side };

// Type for door and valve position.
mtype:pos = { closed, open };

// Datatype to store the status of the doors of a lock.
typedef doorpairs_t {
	mtype:pos west;
	mtype:pos east;
}

// Datatype to store the status of the valves of a lock.
typedef valves_t {
	mtype:pos lower;
	mtype:pos higher;
}

// Orientation of locks
// Needs to be adapted for multiple locks
mtype:lock_orientation LOCK_ORIENTATION[N];

//HARDCODED code
//index control

// Asynchronous channels to handle ship requests.
chan request_west[N] = [M] of { bool };
chan request_east[N] = [M] of { bool };
// Synchronous channels to indicate that a ship has seen that a particular pair
// of doors has opened.
chan observed_west[N] = [0] of { bool };
chan observed_east[N] = [0] of { bool };

// Status of the water level inside a lock.
mtype:level lock_water_level[N];
// Is there a ship currently in the lock?
bool lock_is_occupied[N];

// Status of the ships.
mtype:direction ship_status[M];
// Position of the ships.
byte ship_pos[M]; 
// Number of ships per position.
byte nr_of_ships_at_pos[N+1];

// Status and synchronous channels for doors and valves.
doorpairs_t doors_status[N];
valves_t valve_status[N];
chan change_doors_pos[N] = [0] of { mtype:side };
chan doors_pos_changed[N] = [0] of { bool };
chan change_valve_pos[N] = [0] of { mtype:valve_side };
chan valve_pos_changed[N] = [0] of { bool };


//HEPSI LOCKID MI OLCAK YOKSA LOCKID+1, LOCKID-1 OLCAK MI KONTROL ET
// Lock process type. It reacts to requests to open its doors and valves.
proctype lock(byte lockid) {
	do
	:: change_doors_pos[lockid]?west_side ->
		if
		:: doors_status[lockid].west == closed ->
			doors_status[lockid].west = open;
			if
			:: LOCK_ORIENTATION[lockid] == west_low -> lock_water_level[lockid] = low_level; // Water flows out through western (low) door
			:: LOCK_ORIENTATION[lockid] == east_low && doors_status[lockid].east == closed && valve_status[lockid].lower == closed ->
				lock_water_level[lockid] = high_level; // Water flows in through western (high) door
			:: else -> skip;
			fi;
		:: doors_status[lockid].west == open -> doors_status[lockid].west = closed;
		fi;
		doors_pos_changed[lockid]!true;
	:: change_doors_pos[lockid]?east_side ->
		if
		:: doors_status[lockid].east == closed ->
			doors_status[lockid].east = open;
			if
			:: LOCK_ORIENTATION[lockid] == east_low -> lock_water_level[lockid] = low_level; // Water flows out through eastern (low) door
			:: LOCK_ORIENTATION[lockid] == west_low && doors_status[lockid].west == closed && valve_status[lockid].lower == closed ->
				lock_water_level[lockid] = high_level; // Water flows in through eastern (high) door
			:: else -> skip;
			fi;
		:: doors_status[lockid].east == open -> doors_status[lockid].east = closed;
		fi;
		doors_pos_changed[lockid]!true;
	:: change_valve_pos[lockid]?low_side ->
		if
		:: valve_status[lockid].lower == closed -> valve_status[lockid].lower = open;
			lock_water_level[lockid] = low_level;
		:: valve_status[lockid].lower == open -> valve_status[lockid].lower = closed;
		fi;
		valve_pos_changed[lockid]!true;
	:: change_valve_pos[lockid]?high_side ->
		if
		:: valve_status[lockid].higher == closed -> valve_status[lockid].higher = open;
			if
			:: LOCK_ORIENTATION[lockid] == west_low && doors_status[lockid].west == closed && valve_status[lockid].lower == closed ->
				lock_water_level[lockid] = high_level; // Water flows in as western (low) door is closed
			:: LOCK_ORIENTATION[lockid] == east_low && doors_status[lockid].east == closed && valve_status[lockid].lower == closed ->
				lock_water_level[lockid] = high_level; // Water flows in as eastern (low) door is closed
			:: else -> skip;
			fi;
		:: valve_status[lockid].higher == open -> valve_status[lockid].higher = closed;
		fi;
		valve_pos_changed[lockid]!true;
	od;
}

// Ship process type. Based on its direction and position, it makes requests to open doors,
// and moves when possible.
proctype ship(byte shipid) {
	do
	:: ship_status[shipid] == go_east_to_west && ship_pos[shipid] != 0 ->
		do
		:: doors_status[ship_pos[shipid]-1].east == closed ->
			request_east[ship_pos[shipid]-1]!true;
			atomic { doors_status[ship_pos[shipid]-1].east == open ->
				if
				:: !lock_is_occupied[ship_pos[shipid]-1] ->
						ship_status[shipid] = go_east_to_west_in_lock;
						lock_is_occupied[ship_pos[shipid]-1] = true;
						nr_of_ships_at_pos[ship_pos[shipid]]--;
						observed_east[ship_pos[shipid]-1]!true;
						break;
				:: lock_is_occupied[ship_pos[shipid]-1] ->
						observed_east[ship_pos[shipid]-1]!true;
				fi; }
		:: atomic { doors_status[ship_pos[shipid]-1].east == open &&
			!lock_is_occupied[ship_pos[shipid]-1] ->
				ship_status[shipid] = go_east_to_west_in_lock;
				lock_is_occupied[ship_pos[shipid]-1] = true;
				nr_of_ships_at_pos[ship_pos[shipid]]--;
				break; }
		od;
	:: ship_status[shipid] == go_east_to_west_in_lock ->
		do
		:: doors_status[ship_pos[shipid]-1].west == closed ->
			request_west[ship_pos[shipid]-1]!true;
			atomic { doors_status[ship_pos[shipid]-1].west == open ->
				if
				:: (nr_of_ships_at_pos[ship_pos[shipid]-1] < MAX
					|| ship_pos[shipid]-1 == 0) ->
						ship_status[shipid] = go_east_to_west;
						lock_is_occupied[ship_pos[shipid]-1] = false;
						ship_pos[shipid]--;
						nr_of_ships_at_pos[ship_pos[shipid]]++;
						observed_west[ship_pos[shipid]]!true;
						break;
				:: (nr_of_ships_at_pos[ship_pos[shipid]-1] == MAX
					&& ship_pos[shipid]-1 != 0) ->
						observed_west[ship_pos[shipid]-1]!true;
				fi; }
		:: atomic { doors_status[ship_pos[shipid]-1].west == open &&
			(nr_of_ships_at_pos[ship_pos[shipid]-1] < MAX
			|| ship_pos[shipid]-1 == 0) ->
				ship_status[shipid] = go_east_to_west;
				lock_is_occupied[ship_pos[shipid]-1] = false;
				ship_pos[shipid]--;
				nr_of_ships_at_pos[ship_pos[shipid]]++;
				break; }
		od;
	:: ship_status[shipid] == go_west_to_east && ship_pos[shipid] != N ->
		do
		:: doors_status[ship_pos[shipid]].west == closed ->
			request_west[ship_pos[shipid]]!true;
			atomic { doors_status[ship_pos[shipid]].west == open ->
				if
				:: !lock_is_occupied[ship_pos[shipid]] ->
						ship_status[shipid] = go_west_to_east_in_lock;
						lock_is_occupied[ship_pos[shipid]] = true;
						nr_of_ships_at_pos[ship_pos[shipid]]--;
						observed_west[ship_pos[shipid]]!true;
						break;
				:: lock_is_occupied[ship_pos[shipid]] ->
						observed_west[ship_pos[shipid]]!true;
				fi; }
		:: atomic { doors_status[ship_pos[shipid]].west == open &&
			!lock_is_occupied[ship_pos[shipid]] ->
				ship_status[shipid] = go_west_to_east_in_lock;
				lock_is_occupied[ship_pos[shipid]] = true;
				nr_of_ships_at_pos[ship_pos[shipid]]--;
				break; }
		od;
	:: ship_status[shipid] == go_west_to_east_in_lock ->
		do
		:: doors_status[ship_pos[shipid]].east == closed ->
			request_east[ship_pos[shipid]]!true;
			atomic { doors_status[ship_pos[shipid]].east == open ->
				if
				:: (nr_of_ships_at_pos[ship_pos[shipid]+1] < MAX
					|| ship_pos[shipid]+1 == N) ->
						ship_status[shipid] = go_west_to_east;
						lock_is_occupied[ship_pos[shipid]] = false;
						ship_pos[shipid]++;
						nr_of_ships_at_pos[ship_pos[shipid]]++;
						observed_east[ship_pos[shipid]-1]!true;
						break;
				:: (nr_of_ships_at_pos[ship_pos[shipid]+1] == MAX
					&& ship_pos[shipid]+1 != N) ->
						observed_east[ship_pos[shipid]]!true;
				fi; }
		:: atomic { doors_status[ship_pos[shipid]].east == open &&
			(nr_of_ships_at_pos[ship_pos[shipid]+1] < MAX
			|| ship_pos[shipid]+1 == N) ->
				ship_status[shipid] = go_west_to_east;
				lock_is_occupied[ship_pos[shipid]] = false;
				ship_pos[shipid]++;
				nr_of_ships_at_pos[ship_pos[shipid]]++;
				break; }
		od;
	:: ship_status[shipid] == go_east_to_west && ship_pos[shipid] == 0 ->
		ship_status[shipid] = goal_reached; ship_status[shipid] = go_west_to_east;
	:: ship_status[shipid] == go_west_to_east && ship_pos[shipid] == N ->
		ship_status[shipid] = goal_reached; ship_status[shipid] = go_east_to_west;
	od;
}

proctype main_control(byte lockid) {
	do
	:: request_west[lockid]?[true]->
		:: atomic { !lock_is_occupied[lockid] && doors_status[lockid].west == closed ->
			if 
			::LOCK_ORIENTATION[lockid] == west_low && doors_status[lockid].east == open && valve_status[lockid].higher == closed ->
				change_doors_pos[lockid]!east_side;doors_pos_changed[lockid]?true;
			::LOCK_ORIENTATION[lockid] == west_low && doors_status[lockid].east == closed && valve_status[lockid].higher == open ->	
				change_valve_pos[lockid]!high_side;valve_pos_changed[lockid]?true;
			::LOCK_ORIENTATION[lockid] == west_low && doors_status[lockid].east == open && valve_status[lockid].higher == open ->
				change_doors_pos[lockid]!east_side;doors_pos_changed[lockid]?true;
				change_valve_pos[lockid]!high_side;valve_pos_changed[lockid]?true;
			::LOCK_ORIENTATION[lockid] == west_low && doors_status[lockid].east == closed && valve_status[lockid].higher == closed -> skip	
				if 
                ::LOCK_ORIENTATION[lockid] == west_low && lock_water_level[lockid] != low_level && valve_status[lockid].lower == open  ->
						lock_water_level[lockid] = low_level;
                ::LOCK_ORIENTATION[lockid] == west_low && lock_water_level[lockid] != low_level && valve_status[lockid].lower == closed  ->        
						change_valve_pos[lockid]!low_side;valve_pos_changed[lockid]?true;
                ::LOCK_ORIENTATION[lockid] == west_low && lock_water_level[lockid] == low_level -> skip;      
				fi; 
			::LOCK_ORIENTATION[lockid] == east_low && doors_status[lockid].east == open && valve_status[lockid].lower == closed ->
				change_doors_pos[lockid]!east_side;doors_pos_changed[lockid]?true;
			::LOCK_ORIENTATION[lockid] == east_low && doors_status[lockid].east == closed && valve_status[lockid].lower == open ->
				change_valve_pos[lockid]!low_side;valve_pos_changed[lockid]?true;
			::LOCK_ORIENTATION[lockid] == east_low && doors_status[lockid].east == open && valve_status[lockid].lower == open ->
				change_doors_pos[lockid]!east_side;doors_pos_changed[lockid]?true;
				change_valve_pos[lockid]!low_side;valve_pos_changed[lockid]?true;
			::LOCK_ORIENTATION[lockid] == east_low && doors_status[lockid].east == closed && valve_status[lockid].lower == closed -> skip
				if 
                ::LOCK_ORIENTATION[lockid] == east_low && lock_water_level[lockid] != high_level && valve_status[lockid].higher == open ->
						lock_water_level[lockid] = high_level;
                ::LOCK_ORIENTATION[lockid] == east_low && lock_water_level[lockid] != high_level && valve_status[lockid].higher == closed ->         
						change_valve_pos[lockid]!high_side;valve_pos_changed[lockid]?true;
                ::LOCK_ORIENTATION[lockid] == east_low && lock_water_level[lockid] == high_level -> skip;      
				fi; 	
				change_doors_pos[lockid]!west_side; doors_pos_changed[lockid]?true;
			fi;
		break; }    
			observed_west[lockid]?true;
			lock_is_occupied[lockid] = true;
	:: request_east[lockid]?[true] ->
		:: atomic { !lock_is_occupied[lockid] && doors_status[lockid].east == closed ->
			if 
			::LOCK_ORIENTATION[lockid] == west_low && doors_status[lockid].west == open && valve_status[lockid].lower == closed ->
				change_doors_pos[lockid]!west_side;doors_pos_changed[lockid]?true;
			::LOCK_ORIENTATION[lockid] == west_low && doors_status[lockid].west == closed && valve_status[lockid].lower == open ->	
				change_valve_pos[lockid]!low_side;valve_pos_changed[lockid]?true;
			::LOCK_ORIENTATION[lockid] == west_low && doors_status[lockid].west == open && valve_status[lockid].lower == open ->
				change_doors_pos[lockid]!west_side;doors_pos_changed[lockid]?true;
				change_valve_pos[lockid]!low_side;valve_pos_changed[lockid]?true;
			::LOCK_ORIENTATION[lockid] == west_low && doors_status[lockid].west == closed && valve_status[lockid].lower == closed -> skip	
				if 
                ::LOCK_ORIENTATION[lockid] == west_low && lock_water_level[lockid] != high_level && valve_status[lockid].higher == open ->
						lock_water_level[lockid] = high_level;
                ::LOCK_ORIENTATION[lockid] == west_low && lock_water_level[lockid] != high_level && valve_status[lockid].higher == closed ->        
						change_valve_pos[lockid]!high_side;valve_pos_changed[lockid]?true;
                ::LOCK_ORIENTATION[lockid] == west_low && lock_water_level[lockid] == high_level -> skip;       
				fi; 
			::LOCK_ORIENTATION[lockid] == east_low && doors_status[lockid].west == open && valve_status[lockid].higher == closed ->
				change_doors_pos[lockid]!west_side;doors_pos_changed[lockid]?true;
			::LOCK_ORIENTATION[lockid] == east_low && doors_status[lockid].west == closed && valve_status[lockid].higher == open ->
				change_valve_pos[lockid]!high_side;valve_pos_changed[lockid]?true;
			::LOCK_ORIENTATION[lockid] == east_low && doors_status[lockid].west == open && valve_status[lockid].higher == open ->
				change_doors_pos[lockid]!west_side;doors_pos_changed[lockid]?true;
				change_valve_pos[lockid]!high_side;valve_pos_changed[lockid]?true;
			::LOCK_ORIENTATION[lockid] == east_low && doors_status[lockid].west == closed && valve_status[lockid].higher == closed -> skip
				if 
                ::LOCK_ORIENTATION[lockid] == east_low && lock_water_level[lockid] != low_level && valve_status[lockid].lower == open ->
						lock_water_level[lockid] = low_level;
                ::LOCK_ORIENTATION[lockid] == east_low && lock_water_level[lockid] != low_level && valve_status[lockid].lower == closed ->        
						change_valve_pos[lockid]!low_side;valve_pos_changed[lockid]?true;
                ::LOCK_ORIENTATION[lockid] == east_low && lock_water_level[lockid] == low_level -> skip;       
				fi; 	
			change_doors_pos[lockid]!east_side; doors_pos_changed[lockid]?true;
         fi;   
		break; } 
			observed_east[lockid]?true;
			lock_is_occupied[lockid] = true;  
	od;   
}


proctype monitor() {
    byte lockid;
    lockid = 0;
    do
    :: lockid < N ->
        // // an example assertion.
        // assert(0 <= ship_pos[lockid] && ship_pos[lockid] <= N);

        // (a) The western pairs of doors and the eastern pairs of doors are never simultaneously open.
        assert(!((doors_status[lockid].west == open) && (doors_status[lockid].east == open)));

        // (b1) When the lower pair of doors is open, the higher valve is closed. 
        //assert((LOCK_ORIENTATION == west_low && doors_status.west == open) -> (valve_status.higher == closed));
        assert(!((LOCK_ORIENTATION[lockid] == west_low) && (doors_status[lockid].west == open)) || (valve_status[lockid].higher == closed));
        //Similar assertion but this time for east_low lock orientation.
        assert(!((LOCK_ORIENTATION[lockid] == east_low) && (doors_status[lockid].east == open)) || (valve_status[lockid].higher == closed));

        // (b2) When the higher pair of doors is open, the lower valve is closed.
        //assert((LOCK_ORIENTATION == west_low && doors_status.east == open) -> (valve_status.lower == closed));
        assert(!((LOCK_ORIENTATION[lockid] == east_low) && (doors_status[lockid].west == open)) || (valve_status[lockid].lower == closed));
        //Similar assertion but this time for west_low lock orientation. 
        assert(!((LOCK_ORIENTATION[lockid] == west_low) && (doors_status[lockid].east == open)) || (valve_status[lockid].lower == closed));

        // (c1) The lower pair of doors is only open when the water level in the lock is low.
        //assert(((LOCK_ORIENTATION == west_low) && (doors_status.west == open)) -> (lock_water_level == low_level));
        assert(!((LOCK_ORIENTATION[lockid] == west_low) && (doors_status[lockid].west == open)) || (lock_water_level[lockid] == low_level));
        //Similar assertion but this time for east_low lock orientation.
        assert(!((LOCK_ORIENTATION[lockid] == east_low) && (doors_status[lockid].east == open)) || (lock_water_level[lockid] == low_level));

        // (c2) The higher pair of doors is only open when the water level in the lock is high.
        //assert(((LOCK_ORIENTATION == east_low) && (doors_status.west == open)) -> (lock_water_level == high_level));
        assert(!((LOCK_ORIENTATION[lockid] == east_low) && (doors_status[lockid].west == open)) || (lock_water_level[lockid] == high_level));
        //Similar assertion but this time for west_low lock orientation.
        assert(!((LOCK_ORIENTATION[lockid] == west_low) && (doors_status[lockid].east == open)) || (lock_water_level[lockid] == high_level));
        lockid++;
    :: lockid == N -> skip;
    od;
}

// Initial process that instantiates all other processes and creates
// the initial lock and ship situation.
init {
	byte proc;
	atomic {
		run monitor();
		// In the code below, the individual locks are initialised.
		// The assumption here is that N == 1. When generalising the model for
		// multiple locks, make sure that the do-statement is altered!
		proc = 0;
		do
		:: proc < N ->
            if
            :: proc <= N/2 ->
                LOCK_ORIENTATION[proc] = west_low;
                lock_water_level[proc] = high_level;
            :: proc > N/2 ->
                LOCK_ORIENTATION[proc] = east_low;
                lock_water_level[proc] = low_level;
            fi;        
			doors_status[proc].west = closed;
			doors_status[proc].east = closed;
			valve_status[proc].lower = closed;
			valve_status[proc].higher = closed;
			lock_is_occupied[proc] = false;
			run lock(proc);
            run main_control(proc);
			proc++;
		:: proc == N -> break;
		od;
		// In the code below, the individual ship positions and directions
		// are initialised. Expand this when more ships should be added.
		proc = 0;
		do
        :: proc < M -> 
            if
            :: proc <= M/2 ->
                ship_status[proc] = go_west_to_east; ship_pos[proc] = 0
            :: proc > M/2 ->
                ship_status[proc] = go_east_to_west; ship_pos[proc] = N-1
            fi;    
            run ship(proc);
            proc++;
		:: proc == M -> break;
		od;
		// Do not change the code below! It derives the number of ships per
		// position from the positions of the individual ships.
		proc = 0;
		do
		:: proc < M -> nr_of_ships_at_pos[ship_pos[proc]]++; proc++;
		:: else -> break;
		od;
	}
}