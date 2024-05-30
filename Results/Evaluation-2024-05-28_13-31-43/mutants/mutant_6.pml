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
