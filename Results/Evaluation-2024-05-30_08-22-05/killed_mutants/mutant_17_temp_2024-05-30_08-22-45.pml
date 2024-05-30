#define is_turnA (turn == false)
#define is_turnB (turn == true)
#define flagA_true (flag[0] == true)
#define flagB_true (flag[1] == true)
#define cnt_zero (cnt == 0)
#define cnt_one (cnt == 1)
ltl valid_cnt { [](cnt_zero || cnt_one) }
ltl mutual_exclusion { [](cnt <= 1) }
ltl eventually_A_critical { <>(flagA_true && cnt_one) }
ltl eventually_B_critical { <>(flagB_true && cnt_one) }
ltl turn_taking_A { [](flagA_true -> <> is_turnA) }
ltl turn_taking_B { [](flagB_true -> <> is_turnB) }
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
			:: turn == i;
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
