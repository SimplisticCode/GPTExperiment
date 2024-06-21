#define is_red (state == red)
#define is_green (state == green)
#define is_yellow (state == yellow)
ltl red_until_green { [] is_red -> (is_red U is_green) }
ltl eventually_green { <> is_green }
ltl eventually_yellow { <> is_yellow }
ltl correct_transition_order { [] ((is_red -> <> is_green) && (is_green -> <> is_yellow) && (is_yellow -> <> is_red)) }
mtype = {green, yellow, red}

mtype state = red;

active proctype foo() {
	do
	:: state == red -> state = green;
	:: state == green -> state = yellow;
	:: state == yellow -> state = red;
	od;
}