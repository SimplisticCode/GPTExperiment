#define is_red1 (state1 == red)
#define is_yellow1 (state1 == yellow)
#define is_green1 (state1 == green)
#define is_red2 (state2 == red)
#define is_yellow2 (state2 == yellow)
#define is_green2 (state2 == green)
#define transition1_red_to_green (state1 == red && state2 == yellow -> (state1 == red U state1 == green))
#define transition1_green_to_yellow (state1 == green && state2 == red -> (state1 == green U state1 == yellow))
#define transition1_yellow_to_red (state1 == yellow && state2 == green -> (state1 == yellow U state1 == red))
#define correct_transition2 (state2 == red && state1 == yellow -> state2 == green || state2 == green && state1 == red -> state2 == yellow || state2 == yellow && state1 == green -> state2 == red)
ltl always_valid_states { [] ((is_red1 || is_yellow1 || is_green1) && (is_red2 || is_yellow2 || is_green2)) }
ltl red1_until_green1 { [] (is_red1 -> (is_red1 U is_green1)) }
ltl green1_until_yellow1 { [] (is_green1 -> (is_green1 U is_yellow1)) }
ltl yellow1_until_red1 { [] (is_yellow1 -> (is_yellow1 U is_red1)) }
ltl red2_until_green2 { [] (is_red2 -> (is_red2 U is_green2)) }
ltl green2_until_yellow2 { [] (is_green2 -> (is_green2 U is_yellow2)) }
ltl yellow2_until_red2 { [] (is_yellow2 -> (is_yellow2 U is_red2)) }
ltl eventually_green1 { <> is_green1 }
ltl eventually_yellow1 { <> is_yellow1 }
ltl eventually_red1 { <> is_red1 }
ltl eventually_green2 { <> is_green2 }
ltl eventually_yellow2 { <> is_yellow2 }
ltl eventually_red2 { <> is_red2 }
ltl mutual_exclusion { [] !(is_green1 && is_green2) }
ltl correct_transition1_red_to_green { [] (is_red1 && is_yellow2 -> (is_red1 U is_green1)) }
ltl correct_transition1_green_to_yellow { [] (is_green1 && is_red2 -> (is_green1 U is_yellow1)) }
ltl correct_transition1_yellow_to_red { [] (is_yellow1 && is_green2 -> (is_yellow1 U is_red1)) }
ltl correct_transition2_red_to_green { [] (is_red2 && is_yellow1 -> (is_red2 U is_green2)) }
ltl correct_transition2_green_to_yellow { [] (is_green2 && is_red1 -> (is_green2 U is_yellow2)) }
ltl correct_transition2_yellow_to_red { [] (is_yellow2 && is_green1 -> (is_yellow2 U is_red2)) }
mtype = {red, yellow, green}
mtype state1 = red;
mtype state2 = green;
active proctype light1(){
	do
	:: state1 == red && state2 < yellow;
		state1 = green;
	:: state1 == green && state2 == red;
		state1 = yellow;
	:: state1 == yellow && state2 == green;
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
