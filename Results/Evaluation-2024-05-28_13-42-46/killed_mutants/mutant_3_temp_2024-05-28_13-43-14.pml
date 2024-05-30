#define turn_is_0 (turn == 0)
#define turn_is_1 (turn == 1)
#define flag0_true (flag[0] == true)
#define flag0_false (flag[0] == false)
#define flag1_true (flag[1] == true)
#define flag1_false (flag[1] == false)
#define cnt_is_0 (cnt == 0)
#define cnt_is_1 (cnt == 1)
ltl valid_turn { [](turn_is_0 || turn_is_1) }
ltl valid_flag0 { [](flag0_true || flag0_false) }
ltl valid_flag1 { [](flag1_true || flag1_false) }
ltl valid_cnt { [](cnt_is_0 || cnt_is_1) }
ltl mutual_exclusion { [](cnt_is_1 -> (flag0_true || flag1_true)) }
ltl eventually_critical_section { <> (cnt_is_1) }
ltl always_eventually_turn_change { [] (turn_is_0 -> <> turn_is_1) && [] (turn_is_1 -> <> turn_is_0) }
ltl flag0_true_then_eventually_false { [](flag0_true -> <> flag0_false) }
ltl flag1_true_then_eventually_false { [](flag1_true -> <> flag1_false) }
bool turn;
bool flag[2];
byte cnt;
active proctype ProcessA(){
	int i = 0;
	int j = 1;
	do
	:: true;
		flag[i] = true;
		do
		:: flag[j];
			if
			:: turn == j;
				flag[i] = false;
				!(turn == j);
				flag[i] = true;
			:: else;
			fi;
		:: else;
			break;
		od;
		cnt++;
		assert(cnt == 1);
		cnt--;
		turn = i;
		flag[i] = false;
	od;
}
active proctype ProcessB(){
	int i = 1;
	int j = 0;
	do
	:: true;
		flag[i] = true;
		do
		:: flag[j];
			if
			:: turn == j;
				flag[i] = false;
				!(turn == j);
				flag[i] = true;
			:: else;
			fi;
		:: else;
			break;
		od;
		cnt++;
		assert(cnt == 1);
		cnt--;
		turn = j;
		flag[i] = false;
	od;
}
