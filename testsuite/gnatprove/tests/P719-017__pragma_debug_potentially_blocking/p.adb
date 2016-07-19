with Condition;

package body P is

   procedure Null_Proc is null;

   protected body PT is

      procedure Proc is
      begin
         pragma Debug (Condition, Null_Proc);
      end;
   end;

end;
