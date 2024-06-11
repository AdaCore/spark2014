package Foo with SPARK_Mode is
   protected type T is
      function Get (Y : out Boolean) return Boolean
        with Side_Effects, Depends => ((Y, Get'Result) => T);
      procedure Proc (Y : out Boolean);
      function Simple return Boolean;
   private
      X : Boolean := True;
   end T;
end Foo;
