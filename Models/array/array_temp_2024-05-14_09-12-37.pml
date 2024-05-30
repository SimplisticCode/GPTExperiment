#define is_i_valid (i >= 0 && i <= 4)
#define is_array_correct (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
ltl always_i_valid { [] is_i_valid }
ltl eventually_array_correct { <> is_array_correct }
ltl i_progresses { [] (i < 4 -> <> (i == 4)) }
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
	assert(array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3);
}