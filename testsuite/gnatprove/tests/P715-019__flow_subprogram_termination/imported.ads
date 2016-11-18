with Preconditions; use Preconditions;

package Imported
is
   procedure P_01 with
     Import,
     Convention => C;

   procedure Q_01;

   procedure P_02 with
     Import,
     Convention => C,
     Pre => Nonreturning_Precondition (3, 3);

   procedure Q_02;

end Imported;
