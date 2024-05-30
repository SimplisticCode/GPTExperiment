#define is_i_valid (i >= 0 && i <= 4)
#define is_array_valid (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
ltl valid_i { [] is_i_valid }
ltl eventually_array_valid { <> is_array_valid }
ltl array_initially_zero { [] (i == 0 -> (array[0] == 0 && array[1] == 0 && array[2] == 0 && array[3] == 0)) }
ltl array_progress { [] (i < 4 -> <> (array[i] == i)) }
ltl array_completion { [] (i == 4 -> is_array_valid) }
int array[4];
int i = 0;
active proctype test(){
	do
	:: array[3] < 4;
		array[i] = i;
		i++;
	:: else;
		skip;
	od;
	assert(array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3);
}
