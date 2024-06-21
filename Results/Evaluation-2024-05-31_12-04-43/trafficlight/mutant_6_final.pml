#define is_red (state == red)
#define is_green (state == green)
#define is_yellow (state == yellow)
ltl always_valid_state { [] (is_red || is_green || is_yellow) }
ltl red_until_green { [] is_red -> (is_red U is_green) }
ltl green_until_yellow { [] is_green -> (is_green U is_yellow) }
ltl yellow_until_red { [] is_yellow -> (is_yellow U is_red) }
ltl eventually_red { <> is_red }
ltl eventually_green { <> is_green }
ltl eventually_yellow { <> is_yellow }
ltl no_stuck_in_red { [] (is_red -> <> !is_red) }
ltl no_stuck_in_green { [] (is_green -> <> !is_green) }
ltl no_stuck_in_yellow { [] (is_yellow -> <> !is_yellow) }
ltl correct_transition_order { [] ((is_red -> <> is_green) && (is_green -> <> is_yellow) && (is_yellow -> <> is_red)) }
mtype = {red, yellow, green}
mtype state = red;
active proctype foo(){
	do
	:: state == red;
		state = green;
	:: state == green;
		state = red;
	:: state == yellow;
		state = red;
	od;
}
