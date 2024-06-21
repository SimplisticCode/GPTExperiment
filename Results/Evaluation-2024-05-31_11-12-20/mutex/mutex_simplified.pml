#define x_gt_10 (x > 10)
#define y_lt_5 (y < 5)
ltl eventually_idle { <> (flag[0] == false && flag[1] == false) }
ltl busy_until_idle { [] (flag[0] == true || flag[1] == true) -> ((flag[0] == true || flag[1] == true) U (flag[0] == false && flag[1] == false)) }
ltl x_gt_10_until_y_lt_5 { [] x_gt_10 -> (x_gt_10 U y_lt_5) }

bool turn;
bool flag[2];
byte cnt;
int x;
int y;

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