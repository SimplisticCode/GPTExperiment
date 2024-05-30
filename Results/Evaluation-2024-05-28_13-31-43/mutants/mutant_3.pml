mtype = {red, yellow, green}
mtype state = red;
active proctype foo(){
	do
	:: state == red;
		state = red;
	:: state == green;
		state = yellow;
	:: state == yellow;
		state = red;
	od;
}
