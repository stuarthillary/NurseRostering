using System;
using System.Collections.Generic;
using System.Text;
using Google.OrTools.Sat;

namespace NurseRosteringSAT
{
    public class NurseSolutionObserver : CpSolverSolutionCallback
    {
        public NurseSolutionObserver(IntVar[,,] shifts, int num_nurses, int num_days,
            int num_shifts, HashSet<int> to_print)
        {
            shifts_ = shifts;
            num_nurses_ = num_nurses;
            num_days_ = num_days;
            num_shifts_ = num_shifts;
            to_print_ = to_print;
        }

        public override void OnSolutionCallback()
        {
            solution_count_++;

            if (to_print_.Contains(solution_count_))
            {
                Console.WriteLine(
                    String.Format("Solution #{0}: time = {1:.02} s",
                        solution_count_, WallTime()));
                for (int d = 0; d < num_days_; ++d)
                {
                    Console.WriteLine($"Day #{d}");
                    for (int n = 0; n < num_nurses_; ++n)
                    {
                        for (int s = 0; s < num_shifts_; ++s)
                        {
                            if (BooleanValue(shifts_[n, d, s]))
                            {
                                Console.WriteLine(
                                    $"  Nurse #{n} is working shift #{s}");
                            }
                        }
                    }
                }
            }
        }

        public int SolutionCount()
        {
            return solution_count_;
        }

        private int solution_count_;
        private IntVar[,,] shifts_;
        private int num_nurses_;
        private int num_days_;
        private int num_shifts_;
        private HashSet<int> to_print_;
    }
}
