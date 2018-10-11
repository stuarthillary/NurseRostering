using System;
using System.Linq;
using Google.OrTools.ConstraintSolver;

namespace NurseRosteringCP
{
    class Program
    {
        private static int numberNurses = 4;
        private static int numberShifts = 4; // Nurse assigned to shift 0 means not working that day.
        private static int numberDays = 7;

        static void Main(string[] args)
        {
            var solver = new Solver("schedule_shifts");

            IntVar[,] shifts = createShifts(solver);
            IntVar[,] nurses = createNurses(solver);

            // Set relationships between shifts and nurses.
            setRelationshipBetweenNursesAndShifts(nurses, shifts, solver);

            // Make assignments different on each day
            assignNursesToDifferentShiftsEachDay(nurses, shifts, solver);

            // Each nurse works 5 or 6 days in a week.
            makeNursesWorkFiveOrSixDays(shifts, solver);

            // Create works_shift variables. works_shift[(i, j)] is True if nurse
            // i works shift j at least once during the week.
            IntVar[,] worksShift = createWorksShift(shifts, solver);

            // For each shift (other than 0), at most 2 nurses are assigned to that shift
            // during the week.
            makeMaxTwoNursesForShiftDuringWeek(worksShift, solver);

            // If s nurses works shifts 2 or 3 on, he must also work that shift the previous
            // day or the following day.
            constrainShiftPattern(nurses, solver);

            IntVar[] shiftsFlat = shifts.Flatten();

            // Create the decision builder.
            var db = solver.MakePhase(shiftsFlat,
                    Solver.CHOOSE_FIRST_UNBOUND,
                    Solver.ASSIGN_MIN_VALUE);

            var solution = solver.MakeAssignment();
            solution.Add(shiftsFlat);

            findSolutions(solution, solver, db, shifts);

            Console.ReadKey();
        }

        private static IntVar[,] createShifts(Solver solver)
        {
            var shifts = new IntVar[numberNurses, numberDays];

            for (int n = 0; n < numberNurses; n++)
            {
                for (int d = 0; d < numberDays; d++)
                {
                    shifts[n, d] = solver.MakeIntVar(0, numberShifts - 1, $"shifts({n},{d})");
                }
            }
            return shifts;
        }

        private static IntVar[,] createNurses(Solver solver)
        {
            var nurses = new IntVar[numberShifts, numberDays];

            for (int s = 0; s < numberShifts; s++)
            {
                for (int d = 0; d < numberDays; d++)
                {
                    nurses[s, d] = solver.MakeIntVar(0, numberNurses - 1, $"shift{s} day{d}");
                }
            }
            return nurses;
        }

        private static void setRelationshipBetweenNursesAndShifts(IntVar[,] nurses, IntVar[,] shifts, Solver solver)
        {
            for (int d = 0; d < numberDays; d++)
            {
                var nursesForDay = Enumerable.Range(0, numberShifts).Select(x => nurses[x, d]).ToArray();

                for (int n = 0; n < numberNurses; n++)
                {
                    var s = shifts[n, d];
                    solver.Add(s.IndexOf(nursesForDay) == n);
                }
            }
        }

        private static void assignNursesToDifferentShiftsEachDay(IntVar[,] nurses, IntVar[,] shifts, Solver solver)
        {
            for (int d = 0; d < numberDays; d++)
            {
                IntVarVector x = Enumerable.Range(0, numberNurses).Select(n => shifts[n, d]).ToArray();
                solver.Add(solver.MakeAllDifferent(x));

                IntVarVector y = Enumerable.Range(0, numberShifts).Select(s => nurses[s, d]).ToArray();
                solver.Add(solver.MakeAllDifferent(y));
            }
        }

        private static void makeNursesWorkFiveOrSixDays(IntVar[,] shifts, Solver solver)
        {
            for (int n = 0; n < numberNurses; n++)
            {
                IntVar[] b = new IntVar[numberDays];
                for (int d = 0; d < numberDays; d++)
                {
                    b[d] = (shifts[n, d] > 0).Var();
                }

                solver.Add(solver.MakeSumGreaterOrEqual(b, 5));
                solver.Add(solver.MakeSumLessOrEqual(b, 6));
            }
        }

        private static IntVar[,] createWorksShift(IntVar[,] shifts, Solver solver)
        {
            IntVar[,] worksShift = new IntVar[numberNurses, numberShifts];

            for (int n = 0; n < numberNurses; n++)
            {
                for (int s = 0; s < numberShifts; s++)
                {
                    worksShift[n, s] = solver.MakeBoolVar($"shift{s} nurse{n}");

                    IntVar[] b = new IntVar[numberDays];

                    for (int d = 0; d < numberDays; d++)
                    {
                        b[d] = (shifts[n, d] == s).Var();
                    }

                    solver.Add(worksShift[n, s] == solver.MakeMax(b));
                }
            }

            return worksShift;
        }

        private static void makeMaxTwoNursesForShiftDuringWeek(IntVar[,] worksShift,
            Solver solver)
        {
            for (int s = 1; s < numberShifts; s++)
            {
                IntVar[] b = new IntVar[numberNurses];

                for (int n = 0; n < numberNurses; n++)
                {
                    b[n] = worksShift[n, s];
                }

                solver.Add(solver.MakeSumLessOrEqual(b, 2));
            }
        }

        private static void constrainShiftPattern(IntVar[,] nurses, Solver solver)
        {
            // Explicit constraints
            solver.Add(solver.MakeMax(nurses[2, 0] == nurses[2, 1], nurses[2, 1] == nurses[2, 2]) == 1);
            solver.Add(solver.MakeMax(nurses[2, 1] == nurses[2, 2], nurses[2, 2] == nurses[2, 3]) == 1);
            solver.Add(solver.MakeMax(nurses[2, 2] == nurses[2, 3], nurses[2, 3] == nurses[2, 4]) == 1);
            solver.Add(solver.MakeMax(nurses[2, 3] == nurses[2, 4], nurses[2, 4] == nurses[2, 5]) == 1);
            solver.Add(solver.MakeMax(nurses[2, 4] == nurses[2, 5], nurses[2, 5] == nurses[2, 6]) == 1);
            solver.Add(solver.MakeMax(nurses[2, 5] == nurses[2, 6], nurses[2, 6] == nurses[2, 0]) == 1);
            solver.Add(solver.MakeMax(nurses[2, 6] == nurses[2, 0], nurses[2, 0] == nurses[2, 1]) == 1);
            
            solver.Add(solver.MakeMax(nurses[3, 0] == nurses[3, 1], nurses[3, 1] == nurses[3, 2]) == 1);
            solver.Add(solver.MakeMax(nurses[3, 1] == nurses[3, 2], nurses[3, 2] == nurses[3, 3]) == 1);
            solver.Add(solver.MakeMax(nurses[3, 2] == nurses[3, 3], nurses[3, 3] == nurses[3, 4]) == 1);
            solver.Add(solver.MakeMax(nurses[3, 3] == nurses[3, 4], nurses[3, 4] == nurses[3, 5]) == 1);
            solver.Add(solver.MakeMax(nurses[3, 4] == nurses[3, 5], nurses[3, 5] == nurses[3, 6]) == 1);
            solver.Add(solver.MakeMax(nurses[3, 5] == nurses[3, 6], nurses[3, 6] == nurses[3, 0]) == 1);
            solver.Add(solver.MakeMax(nurses[3, 6] == nurses[3, 0], nurses[3, 0] == nurses[3, 1]) == 1);

            // Loop achieves the same constraints

            //foreach (var shift in new[] { 2, 3 })
            //{
            //    for (int d = 0; d < numberDays; d++)
            //    {
            //        int nextDay = (d + 1) % 7;
            //        int dayAfterNext = (d + 2) % 7;

            //        solver.Add(solver.MakeMax(nurses[shift, d] == nurses[shift, nextDay], nurses[shift, nextDay] == nurses[shift, dayAfterNext]) == 1);
            //    }
            //}
        }

        private static void findSolutions(Assignment solution, Solver solver, DecisionBuilder db, IntVar[,] shifts)
        {
            // Create the solution collector.
            var collector = solver.MakeAllSolutionCollector(solution);

            try
            {
                solver.Solve(db, collector);
            }
            catch (Exception ex)
            {
            }

            Console.WriteLine("Solutions found: {0}", collector.SolutionCount());
            Console.WriteLine("Time: {0} ms", solver.WallTime());
            Console.WriteLine();

            // Display a few solutions picked at random.
            var aFewSolutions = new[] { 859, 2034, 5091, 7003 };
            foreach (int i in aFewSolutions)
            {
                Console.WriteLine("Solution number {0}\n", i);

                for (int d = 0; d < numberDays; d++)
                {
                    Console.WriteLine("Day {0}", d);

                    for (int n = 0; n < numberNurses; n++)
                    {
                        Console.WriteLine("Nurse {0} assigned to task {1}", n, collector.Value(i, shifts[n, d]));
                    }
                }

                Console.WriteLine();
            }
        }
    }
}
