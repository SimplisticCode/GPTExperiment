Model to Fix:

mtype = {green, yellow, red}
mtype state = red;
active proctype foo() {
    do
    :: state == red -> state = green;
    :: state == green -> state = yellow;
    :: state == yellow -> state = red;
    od;
}

Macros: {
    is_red: (state == red),
    is_yellow: (state == yellow),
    is_green: (state == green)
}
Specification: {
    red_until_yellow: [] (is_red -> (is_red U is_yellow)),
    cycles_through_all: [] (<> is_red && <> is_green && <> is_yellow)
}
Bisimilarity: {mutant1.pml, mutant2.pml}

mtype = {levelMsg, stop, methanestop, alarm, running, commandMsg, start, alarmMsg, high, low, stopped, medium, ready, lowstop}
chan cCmd = [0] of {mtype};
chan cAlarm = [0] of {mtype};
chan cMethane = [0] of {mtype};
chan cLevel = [0] of {mtype};
mtype pstate = stopped;
mtype readMsg = commandMsg;
bool pumpOn = false;
bool methane = false;
mtype waterLevel = medium;
mtype uwants = stop;
mtype level = medium;

active proctype controller(){
    mtype pcommand = start;
    do
    ::	atomic {
            cCmd?pcommand;
            readMsg = commandMsg;
        };
        if
        ::	pcommand == stop;
            if
            ::	atomic {
                    pstate == running;
                    pumpOn = false;
                };
            ::	else;
                skip;
            fi;
            pstate = stopped;
        ::	pcommand == start;
            if
            ::	atomic {
                    pstate != running;
                    pstate = ready;
                };
            ::	else;
                skip;
            fi;
        ::	else;
            assert((false));
        fi;
        cCmd!pstate;
    ::	atomic {
            cAlarm?_;
            readMsg = alarmMsg;
        };
        if
        ::	atomic {
                pstate == running;
                pumpOn = false;
            };
        ::	else;
            skip;
        fi;
        pstate = methanestop;
    ::	atomic {
            cLevel?level;
            readMsg = levelMsg;
        };
        if
        ::	level == high;
            if
            ::	pstate == ready || pstate == lowstop;
                atomic {
                    cMethane!pstate;
                    cMethane?pstate;
                    if
                    ::	pstate == ready;
                        pstate = running;
                        pumpOn = true;
                    ::	else;
                        skip;
                    fi;
                };
            ::	else;
                skip;
            fi;
        ::	level == low;
            if
            ::	atomic {
                    pstate == running;
                    pumpOn = false;
                    pstate = lowstop;
                };
            ::	else;
                skip;
            fi;
        ::	level == medium;
            skip;
        fi;
    od;
}
active proctype user(){
    do
    ::	
    atomic {
        if
        ::	uwants = start;
        ::	uwants = stop;
        fi;
        cCmd!uwants;
        cCmd?_;
    };
    od;
}
active proctype methanealarm(){
    do
    ::	methane = true;
        cAlarm!alarm;
    ::	methane = false;
    od;
}
active proctype methanesensor(){
    do
    ::	atomic {
            cMethane?_;
            if
            ::	methane;
                cMethane!methanestop;
            ::	!methane;
                cMethane!ready;
            fi;
        };
    od;
}
active proctype watersensor(){
    do
    ::	atomic {
            if
            ::	waterLevel == low;
                if
                ::	waterLevel = low;
                ::	waterLevel = medium;
                fi;
            ::	waterLevel == medium;
                if
                ::	waterLevel = low;
                ::	waterLevel = medium;
                ::	waterLevel = high;
                fi;
            ::	waterLevel == high;
                if
                ::	waterLevel = medium;
                ::	waterLevel = high;
                fi;
            fi;
            cLevel!waterLevel;
        };
    od;
}

Macros: {
    is_lowstop: (pstate == lowstop),
    is_commandMsg: (readMsg == commandMsg),
    is_alarmMsg: (readMsg == alarmMsg),
    is_levelMsg: (readMsg == levelMsg),
    is_high: (level == high),
    is_medium: (level == medium),
    is_low: (level == low),
    pump_on: (pumpOn == true),
    pump_off: (pumpOn == false),
    methane_present: (methane == true),
    methane_absent: (methane == false),
    user_wants_start: (readMsg == start),
    user_wants_stop: (readMsg == stop)
}
Specification: {
    valid_pstate: [] (is_stopped || is_running || is_ready || is_methanestop || is_lowstop),
    valid_readMsg: [] (is_commandMsg || is_alarmMsg || is_levelMsg),
    valid_waterLevel: [] (is_high || is_medium || is_low),
    valid_pumpOn: [] (pump_on || pump_off),
    alarm_leads_to_stop: [] (is_alarmMsg -> <> pump_off),
    user_start_leads_to_ready_or_running: [] (user_wants_start -> (user_wants_start U (is_ready || is_running))),
    user_stop_leads_to_pump_off: [] (user_wants_stop -> <> pump_off),
    pump_on_system_running: [] (pump_on -> is_running),
    low_water_level_leads_to_pumpstop: [] ((is_levelMsg && is_low) -> <> pump_off),
    high_water_level_leads_to_pumpstart: [] ((is_levelMsg && is_high) -> <> (pump_on || is_methanestop)),
    high_metane_leads_to_pumpstop: [] (is_methanestop -> <> pump_off)
}
Bisimilarity: []

mtype = {red, yellow, green}
mtype state1 = red;
mtype state2 = green;
active proctype light1(){
    do
    :: state1 == red && state2 == yellow;
        state1 = green;
    :: state1 == green && state2 == red;
        state1 = yellow;
    :: state2 == yellow && state2 == green;
        state1 = red;
    od;
}
active proctype light2(){
    do
    :: state2 == red && state1 == yellow;
        state2 = green;
    :: state2 == green && state1 == red;
        state2 = yellow;
    :: state2 == yellow && state1 == green;
        state2 = red;
    od;
}

Macros: {
    is_red1: (state1 == red),
    is_yellow1: (state1 == yellow),
    is_green1: (state1 == green),
    is_red2: (state2 == red),
    is_yellow2: (state2 == yellow),
    is_green2: (state2 == green)
}
Specification: {
    always_valid_states: [] ((is_red1 || is_yellow1 || is_green1) && (is_red2 || is_yellow2 || is_green2)),
    red1_until_green1: [] (is_red1 -> (is_red1 U is_green1)),
    green1_until_yellow1: [] (is_green1 -> (is_green1 U is_yellow1)),
    yellow1_until_red1: [] (is_yellow1 -> (is_yellow1 U is_red1)),
    red2_until_green2: [] (is_red2 -> (is_red2 U is_green2)),
    green2_until_yellow2: [] (is_green2 -> (is_green2 U is_yellow2)),
    yellow2_until_red2: [] (is_yellow2 -> (is_yellow2 U is_red2)),
    eventually_green1: <> is_green1,
    eventually_yellow1: <> is_yellow1,
    eventually_red1: <> is_red1,
    eventually_green2: <> is_green2,
    eventually_yellow2: <> is_yellow2,
    eventually_red2: <> is_red2,
    mutual_exclusion: [] !(is_green1 && is_green2)
}
Bisimilarity: []

int array[4];
int i = 0;

active proctype test (){
    do
    :: i < 4 ->
        array[i] = i;
        i++;
    :: else ->
        skip;
    od;
}

Macros: {
    array_correct: (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3),
    array_unchanged: (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
}
Specification: {
    valid_i_range: [] (i >= 0 && i <= 4),
    eventually_array_set_correctly: <> (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3),
    i_stops_at_4: [] (i == 4 -> [] (i == 4)),
    array_values_unchanged: [] ((array[0] == 0) && (array[1] == 1) && (array[2] == 2) && (array[3] == 3))
}