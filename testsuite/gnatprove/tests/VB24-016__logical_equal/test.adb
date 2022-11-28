procedure Test with SPARK_Mode is
   package Nested is
      type T1 is private;
      type T2 is private;
      type T3 is private;
      function "=" (X, Y : T3) return Boolean;
   private
      pragma SPARK_Mode (Off);
      type T1 is new Integer;
      type T2 is new Float;
      type T3 is new Integer;
      function "=" (X, Y : T3) return Boolean is (True);
   end Nested;
   use Nested;

   type T4 is new Integer;
   type T5 is new Float;

   function My_Eq (X, Y : T1) return Boolean with
     Ghost,
     Annotate => (GNATprove, Logical_Equal);-- @INLINE_ANNOTATION:PASS
   function My_Eq (X, Y : T1) return Boolean is (X = Y);

   function My_Eq (X, Y : T2) return Boolean with
     Ghost,
     Annotate => (GNATprove, Logical_Equal);-- @INLINE_ANNOTATION:FAIL
   function My_Eq (X, Y : T2) return Boolean is (X = Y);

   function My_Eq (X, Y : T3) return Boolean with
     Ghost,
     Annotate => (GNATprove, Logical_Equal);-- @INLINE_ANNOTATION:FAIL
   function My_Eq (X, Y : T3) return Boolean is (X = Y);

   function My_Eq (X, Y : T4) return Boolean with
     Ghost,
     Annotate => (GNATprove, Logical_Equal);-- @INLINE_ANNOTATION:PASS
   function My_Eq (X, Y : T4) return Boolean is (X = Y);

   function My_Eq (X, Y : T5) return Boolean with
     Ghost,
     Annotate => (GNATprove, Logical_Equal); -- @INLINE_ANNOTATION:FAIL
   function My_Eq (X, Y : T5) return Boolean is (X = Y);
begin
   null;
end Test;
