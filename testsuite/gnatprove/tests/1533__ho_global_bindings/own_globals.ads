--  Exercise the specialized function's own globals, with a callback that has
--  no globals. Generation inside an Inline_For_Proof definition must restore
--  the mutable binding of Flag as well.

package Own_Globals with SPARK_Mode is
   Flag : Boolean := False;

   function Always_False return Boolean is (False);

   function Eval (Callback : not null access function return Boolean)
     return Boolean
   is (Callback.all xor Flag)
   with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Post => Eval'Result = (Callback.all xor Flag);

   function Wrapped return Boolean with
     Post => Wrapped'Result = Eval (Always_False'Access),
     Annotate => (GNATprove, Inline_For_Proof);

   procedure Check;
end Own_Globals;
