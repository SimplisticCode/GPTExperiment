#define valid_i (i >= 0 && i <= 4)
#define array_0_set (array[0] == 0)
#define array_1_set (array[1] == 1)
#define array_2_set (array[2] == 2)
#define array_3_set (array[3] == 3)
#define array_correct (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
#define array_1_not_exceed (array[1] <= 1)
#define array_1_correct (array[1] == 1)
ltl valid_i_range { [] valid_i }
ltl eventually_array_0_set { <> array_0_set }
ltl eventually_array_1_set { <> array_1_set }
ltl eventually_array_2_set { <> array_2_set }
ltl eventually_array_3_set { <> array_3_set }
ltl array_elements_set_in_order { [] (i == 0 -> <> array_0_set) && (i == 1 -> <> array_1_set) && (i == 2 -> <> array_2_set) && (i == 3 -> <> array_3_set) }
ltl final_assertion { [] (i == 4 -> array_correct) }
ltl always_array_1_not_exceed { [] array_1_not_exceed }
ltl eventually_array_1_correct { <> array_1_correct }
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
