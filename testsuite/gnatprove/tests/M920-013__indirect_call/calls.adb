pragma SPARK_Mode;

package body Calls is

   package body Inner is
      procedure C1 is begin null; end;

      task body T is
      begin
         accept C2;
      end;

      protected body P is
         procedure C3 is begin null; end;
      end;

      procedure C4 (X : R'Class) is begin null; end;
   end Inner;

   procedure C is
   begin
      --  call through access to subprogram
      Inner.PC1.all;

      --  entry call
      Inner.T.C2;

      --  call to protected object
      Inner.P.C3;

      --  dispatching call
      Inner.Y.C4;
   end C;
end Calls;
