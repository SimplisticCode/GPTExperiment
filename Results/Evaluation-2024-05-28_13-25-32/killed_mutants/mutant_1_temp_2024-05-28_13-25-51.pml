#define is_red (state == red)
#define is_green (state == green)
#define is_yellow (state == yellow)
ltl always_valid_states { [] (is_red || is_green || is_yellow) }
ltl red_until_green { [] is_red -> (is_red U is_green) }
ltl green_until_yellow { [] is_green -> (is_green U is_yellow) }
ltl yellow_until_red { [] is_yellow -> (is_yellow U is_red) }
ltl cycles_through_all { [] (<> is_red && <> is_green && <> is_yellow) }
mtype = {red, yellow, green}
mtype state = red;
active proctype foo(){
	do
	:: state <= red;
		state = green;
	:: state == green;
		state = yellow;
	:: state == yellow;
		state = red;
	od;
}
