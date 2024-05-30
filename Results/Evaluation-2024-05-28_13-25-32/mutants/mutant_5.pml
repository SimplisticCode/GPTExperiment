mtype = {red, yellow, green}
mtype state = red;
active proctype foo(){
	do
	:: state == red;
		state = green;
	:: state == red;
		state = yellow;
	:: state == yellow;
		state = red;
	od;
}
