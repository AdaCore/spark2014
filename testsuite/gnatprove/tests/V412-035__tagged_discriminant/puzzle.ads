with Solution;

package Puzzle with SPARK_Mode is

   type Instance (Max_Words : Integer) is tagged private;

   procedure Try_Set_Word (This : in out Instance);

private

   type Instance (Max_Words : Integer) is tagged record
      Sol :  Solution.Instance (Max_Words);
   end record;

end Puzzle;
