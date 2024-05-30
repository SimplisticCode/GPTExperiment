#define i_in_bounds (i >= 0 && i <= 4)
#define array_correct (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
ltl valid_index { [] i_in_bounds }
ltl eventually_i_max { <> (i == 4) }
ltl eventually_array_correct { <> array_correct }
ltl eventually_array_correct_final { [] (i == 4 -> array_correct) }
int array[4];
int i = 0;
active proctype test(){
	do
	:: i < 4;
		array[i] = i;
		array[1]++;
	:: else;
		skip;
	od;
	assert(array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3);
}
