#define is_turn_0 (turn == false)
#define is_turn_1 (turn == true)
#define flag_0_true (flag[0] == true)
#define flag_0_false (flag[0] == false)
#define flag_1_true (flag[1] == true)
#define flag_1_false (flag[1] == false)
#define cnt_0 (cnt == 0)
#define cnt_1 (cnt == 1)
ltl valid_cnt { [](cnt_0 || cnt_1) }
ltl valid_flags { []((flag_0_true || flag_0_false) && (flag_1_true || flag_1_false)) }
ltl valid_turn { [](is_turn_0 || is_turn_1) }
ltl process_a_enters_critical { [](flag_0_true -> <> cnt_1) }
ltl process_b_enters_critical { [](flag_1_true -> <> cnt_1) }
ltl process_a_exits_critical { [](cnt_1 && flag_0_true -> <> cnt_0) }
ltl process_b_exits_critical { [](cnt_1 && flag_1_true -> <> cnt_0) }
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
		turn = j;
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
				flag[i] = false;
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
