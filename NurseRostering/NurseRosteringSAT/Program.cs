using System;
using System.Collections.Generic;
using System.Linq;
using Google.OrTools.Sat;

namespace NurseRosteringSAT
{
    class Program
    {
        static void Main(string[] args)
        {
            Solve();
        }

        static void Solve()
        {
            // Data.
            int num_nurses = 4;
            // Nurse assigned to shift 0 means not working that day.
            int num_shifts = 4;
            int num_days = 7;

            var all_nurses = Enumerable.Range(0, num_nurses);
            var all_shifts = Enumerable.Range(0, num_shifts);
            var all_working_shifts = Enumerable.Range(1, num_shifts - 1);
            var all_days = Enumerable.Range(0, num_days);

            // Creates the model.
            CpModel model = new CpModel();

            // Creates shift variables.
            // shift[n, d, s]: nurse "n" works shift "s" on day "d".
            IntVar[,,] shift = new IntVar[num_nurses, num_days, num_shifts];
            foreach (int n in all_nurses)
            {
                foreach (int d in all_days)
                {
                    foreach (int s in all_shifts)
                    {
                        shift[n, d, s] =
                            model.NewBoolVar(String.Format("shift_n{0}d{1}s{2}", n, d, s));
                    }
                }
            }

            // Makes assignments different on each day, that is each shift is
            // assigned at most one nurse. As we have the same number of
            // nurses and shifts, then each day, each shift is assigned to
            // exactly one nurse.
            foreach (int d in all_days)
            {
                foreach (int s in all_shifts)
                {
                    IntVar[] tmp = new IntVar[num_nurses];
                    foreach (int n in all_nurses)
                    {
                        tmp[n] = shift[n, d, s];
                    }
                    model.Add(tmp.Sum() == 1);
                }
            }

            // Nurses do 1 shift per day.
            foreach (int n in all_nurses)
            {
                foreach (int d in all_days)
                {
                    IntVar[] tmp = new IntVar[num_shifts];
                    foreach (int s in all_shifts)
                    {
                        tmp[s] = shift[n, d, s];
                    }
                    model.Add(tmp.Sum() == 1);
                }
            }

            // Each nurse works 5 or 6 days in a week.
            // That is each nurse works shift 0 at most 2 times.
            foreach (int n in all_nurses)
            {
                IntVar[] tmp = new IntVar[num_days];
                foreach (int d in all_days)
                {
                    tmp[d] = shift[n, d, 0];
                }
                model.Add(1 <= tmp.Sum() <= 2);
            }

            // works_shift[(n, s)] is 1 if nurse n works shift s at least one day in
            // the week.
            IntVar[,] works_shift = new IntVar[num_nurses, num_shifts];
            foreach (int n in all_nurses)
            {
                foreach (int s in all_shifts)
                {
                    works_shift[n, s] =
                        model.NewBoolVar(String.Format("works_shift_n{0}s{1}", n, s));
                    IntVar[] tmp = new IntVar[num_days];
                    foreach (int d in all_days)
                    {
                        tmp[d] = shift[n, d, s];
                    }
                    model.AddMaxEquality(works_shift[n, s], tmp);
                }
            }

            // For each working shift, at most 2 nurses are assigned to that shift
            // during the week.
            foreach (int s in all_working_shifts)
            {
                IntVar[] tmp = new IntVar[num_nurses];
                foreach (int n in all_nurses)
                {
                    tmp[n] = works_shift[n, s];
                }
                model.Add(tmp.Sum() <= 2);
            }

            // If a nurse works shifts 2 or 3 on, she must also work that
            // shift the previous day or the following day.  This means that
            // on a given day and shift, either she does not work that shift
            // on that day, or she works that shift on the day before, or the
            // day after.
            foreach (int n in all_nurses)
            {
                for (int s = 2; s <= 3; ++s)
                {
                    foreach (int d in all_days)
                    {
                        int yesterday = d == 0 ? num_days - 1 : d - 1;
                        int tomorrow = d == num_days - 1 ? 0 : d + 1;
                        model.AddBoolOr(new ILiteral[] { shift[n, yesterday, s],
                                           shift[n, d, s].Not(),
                                           shift[n, tomorrow, s] });
                    }
                }
            }

            // Creates the solver and solve.
            CpSolver solver = new CpSolver();
            solver.StringParameters = ""; // Bug in current version, callback not called unless StringParameters not null
            // Display a few solutions picked at random.
            HashSet<int> to_print = new HashSet<int>();
            to_print.Add(859);
            to_print.Add(2034);
            to_print.Add(5091);
            to_print.Add(7003);
            NurseSolutionObserver cb = new NurseSolutionObserver(
                shift, num_nurses, num_days, num_shifts, to_print);
            CpSolverStatus status = solver.SearchAllSolutions(model, cb);

            // Statistics.
            Console.WriteLine("Statistics");
            Console.WriteLine(String.Format("  - solve status    : {0}", status));
            Console.WriteLine("  - conflicts       : " + solver.NumConflicts());
            Console.WriteLine("  - branches        : " + solver.NumBranches());
            Console.WriteLine("  - wall time       : " + solver.WallTime() + " ms");
            Console.WriteLine("  - #solutions      : " + cb.SolutionCount());

            Console.ReadKey();
        }
    }
}
