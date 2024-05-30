mtype = {red, yellow, green}
mtype state = red;
active proctype foo(){
	do
	:: state == green;
		state = green;
	:: state == green;
		state = yellow;
	:: state == yellow;
		state = red;
	od;
}
