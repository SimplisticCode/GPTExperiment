#define valid_i (i >= 0 && i <= 4)
#define array_correct (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
ltl valid_i_property { [] valid_i }
ltl array_correct_property { [] (i == 4 -> array_correct) }
ltl eventually_correct_array { <> array_correct }
int array[4];
int i = 0;
active proctype test(){
	do
	:: i < 4;
		array[i] = array[3];
		i++;
	:: else;
		skip;
	od;
	assert(array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3);
}
