with Preconditions; use Preconditions;

package Imported
is
   procedure P_01 with
     Import,
     Convention => C;

   procedure Q_01 with Always_Terminates;

   procedure P_02 with
     Import,
     Convention => C,
     Pre => Nonreturning_Precondition (3, 3);

   procedure Q_02 with Always_Terminates;

end Imported;
