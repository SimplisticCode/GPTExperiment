int array[4];
int i = 0;

active proctype test (){
	do
	:: i < 4 ->
		array[i] = i;
		i++;
	:: else ->
		skip;
	od;
}