#define is_red (state == red)
#define is_green (state == green)
#define is_yellow (state == yellow)
ltl valid_states { [](is_red || is_green || is_yellow) }
ltl red_to_green { [](is_red -> <> is_green) }
ltl green_to_yellow { [](is_green -> <> is_yellow) }
ltl yellow_to_red { [](is_yellow -> <> is_red) }
ltl cycle_through_all { []<>(is_red && <> is_green && <> is_yellow) }
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
