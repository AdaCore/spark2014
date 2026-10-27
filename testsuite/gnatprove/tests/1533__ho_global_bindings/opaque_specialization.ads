with Opaque_State;

--  Exercise specialization generation inside Inline_For_Proof definitions.
--  Generated program declarations must use mutable bindings for callback
--  globals, for both opaque globals and ordinary Ada objects.

package Opaque_Specialization with SPARK_Mode is
   function Read return Integer with
     Import, Global => (Input => Opaque_State.State);

   procedure Change with
     Import, Global => (In_Out => Opaque_State.State);

   Visible : Integer := 0;
   function Read_Visible return Integer is (Visible);

   function Eval (Callback : not null access function return Integer)
     return Integer
   is (Callback.all)
   with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Post => Eval'Result = Callback.all;

   function Wrapped return Integer with
     Post => Wrapped'Result = Eval (Read'Access),
     Annotate => (GNATprove, Inline_For_Proof);

   function Wrapped_Visible return Integer with
     Post => Wrapped_Visible'Result = Eval (Read_Visible'Access),
     Annotate => (GNATprove, Inline_For_Proof);

   procedure Check;
   procedure Check_Change;
   procedure Check_Visible;
end Opaque_Specialization;
