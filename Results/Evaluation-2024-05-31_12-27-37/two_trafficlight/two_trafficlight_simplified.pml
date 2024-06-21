#define is_red1 (state1 == red)
#define is_yellow1 (state1 == yellow)
#define is_green1 (state1 == green)
#define is_red2 (state2 == red)
#define is_yellow2 (state2 == yellow)
#define is_green2 (state2 == green)
ltl red1_until_green1 { [] is_red1 -> (is_red1 U is_green1) }
ltl eventually_green1 { <> is_green1 }
ltl eventually_yellow1 { <> is_yellow1 }
ltl eventually_red2 { <> is_red2 }
ltl eventually_yellow2 { <> is_yellow2 }
ltl mutual_exclusion { [] !(is_green1 && is_green2) }
ltl red1_yellow2_until_green1 { [] ((is_red1 && is_yellow2) -> <> is_green1) }
ltl green1_red2_until_yellow1 { [] ((is_green1 && is_red2) -> <> is_yellow1) }




mtype = {green, yellow, red}

mtype state1 = red;
mtype state2 = green;

active proctype light1() {
	do
	:: state1 == red  && state2 == yellow -> state1 = green;
	:: state1 == green && state2 == red -> state1 = yellow;
	:: state1 == yellow && state2 == green -> state1 = red;
	od;
}

active proctype light2() {
	do
	:: state2 == red && state1 == yellow -> state2 = green;
	:: state2 == green && state1 == red -> state2 = yellow;
	:: state2 == yellow && state1 == green -> state2 = red;
	od;
}