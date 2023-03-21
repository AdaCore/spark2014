with Ada.Real_Time;

package body P is
   package body Q is
      procedure Process (X : T) is
      begin
         null;
      end Process;
   end Q;

   package body R is
      procedure Process (X : TT) is
      begin
         null;
      end Process;
   end R;

   procedure Proxy is
      X : Q.T'Class := R.TT'(C => 0, CC => 0);
   begin
      Q.Process (X);
   end;

   protected body PT is
      procedure Proc (X : Q.T'Class; Y : Q.T) is
         Now : constant Ada.Real_Time.Time := Ada.Real_Time.Clock;
      begin
         delay until Now;
         Q.Process (X);  --  dispatching call
         Q.Process (Y);  --  non-dispatching call
         Proxy;
      end Proc;
   end PT;
end P;
