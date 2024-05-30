#define is_turnA (turn == false)
#define is_turnB (turn == true)
#define flagA_true (flag[0] == true)
#define flagB_true (flag[1] == true)
#define cnt_zero (cnt == 0)
#define cnt_one (cnt == 1)
#define flagA_false (flag[0] == false)
#define flagB_false (flag[1] == false)
ltl valid_cnt { [](cnt_zero || cnt_one) }
ltl mutual_exclusion { [](cnt <= 1) }
ltl eventually_A_critical { <>(flagA_true && cnt_one) }
ltl eventually_B_critical { <>(flagB_true && cnt_one) }
ltl turn_taking_A { [](flagA_true -> <> is_turnA) }
ltl turn_taking_B { [](flagB_true -> <> is_turnB) }
ltl flagA_reset { [](cnt_zero -> <> flagA_false) }
ltl flagB_reset { [](cnt_zero -> <> flagB_false) }
ltl eventually_flagA_reset { [] (flagA_true -> <> flagA_false) }
ltl eventually_flagB_reset { [] (flagB_true -> <> flagB_false) }
bool turn;
bool flag[2];
byte cnt;

active proctype ProcessA()
{
    int i = 0; // Assuming process A has a fixed id of 0
    int j = 1;
    do
    :: true -> // Replaces the againA label for repetition
        flag[i] = true;
        do
        :: flag[j] ->
            if
            :: turn == j ->
                flag[i] = false;
                !(turn == j);
                flag[i] = true
            :: else
            fi
        :: else ->
            break
        od;

        cnt++;
        assert(cnt == 1); /* critical section */
        cnt--;

        turn = j;
        flag[i] = false;
    od; // End of outer loop for continuous execution
}

active proctype ProcessB()
{
    int i = 1; // Assuming process B has a fixed id of 1
    int j = 0;
    do
    :: true -> // Replaces the againB label for repetition
        flag[i] = true;
        do
        :: flag[j] ->
            if
            :: turn == j ->
                flag[i] = false;
                !(turn == j);
                flag[i] = true
            :: else
            fi
        :: else ->
            break
        od;

        cnt++;
        assert(cnt == 1); /* critical section */
        cnt--;

        turn = j;
        flag[i] = false;
    od; // End of outer loop for continuous execution
}