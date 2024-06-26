#define is_red (state == red)
#define is_yellow (state == yellow)
#define is_green (state == green)
ltl always_valid_state { [] (is_red || is_yellow || is_green) }
ltl red_until_green { [] is_red -> (is_red U is_green) }
ltl green_until_yellow { [] is_green -> (is_green U is_yellow) }
ltl yellow_until_red { [] is_yellow -> (is_yellow U is_red) }
ltl eventually_red { <> is_red }
ltl eventually_green { <> is_green }
ltl eventually_yellow { <> is_yellow }
mtype = {red, yellow, green}
mtype state = red;
active proctype foo(){
	do
	:: state == red;
		state = green;
	:: state == green;
		state = yellow;
	:: state == green;
		state = red;
	od;
}
