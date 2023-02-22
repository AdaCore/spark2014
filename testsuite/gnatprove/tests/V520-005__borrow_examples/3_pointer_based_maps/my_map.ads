package My_Map with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Map is private with Default_Initial_Condition => False;
   type Map_Acc is access Map;

   function Model_Contains (M : access constant Map; K : Positive) return Boolean
   with
     Ghost,
     Subprogram_Variant => (Structural => M);
   --  Return True iff there is mapping for K in M. This is a specification
   --  function encoded in a recursive way.

   function Model_Value (M : access constant Map; K : Positive) return Integer
   with
     Ghost,
     Subprogram_Variant => (Structural => M),
     Pre => Model_Contains (M, K);
   --  Return the mapping associated to K in M. This is a specification
   --  function encoded in a recursive way.

   function At_End
     (M : access constant Map) return access constant Map
   is
     (M)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);
   --  Pledge function, used to mark assertions as pledges for the analysis tool

   function At_End
     (I : access constant Integer) return access constant Integer
   is
     (I)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);
   --  Pledge function, used to mark assertions as pledges for the analysis tool

   function Contains (M : access constant Map; K : Positive) return Boolean with
     Post => Contains'Result = Model_Contains (M, K);
   --  The imperative version of Model_Contains

   procedure Replace_Element (M : access Map; K : Positive; V : Integer) with
     Pre  => Model_Contains (M, K),
     Post => Model_Contains (M, K) and then Model_Value (M, K) = V;
   --  Replace the element associated to K in M by V.
   --  The specification is partial, we do not attempt to show that other keys
   --  are preserved.

   function Constant_Access (M : access constant Map; K : Positive) return not null access constant Integer with
     Pre  => Model_Contains (M, K),
     Post => Model_Value (M, K) = Constant_Access'Result.all;
   --  Return a constant access to the value associated to K by M

   function Reference (M : access Map; K : Positive) return not null access Integer with
     Pre  => Model_Contains (M, K),
     Post => Model_Value (M, K) = Reference'Result.all and then
       Model_Contains (At_End (M), K) and then
       Model_Value (At_End (M), K) = At_End (Reference'Result).all;
   --  Borrow the value associated to K by M.
   --  The specification is partial, we do not attempt to show that other keys
   --  are frozen by the borrow.

private
   type Int_Acc is not null access Integer;
   type Map is record
      Key   : Positive := 1;
      Value : Int_Acc;
      Next  : Map_Acc;
   end record;
   --  Maps are encoded as a list of pairs of a key and a value. For the value
   --  we use an access type so that it can be borrowed.

   function Model_Contains (M : access constant Map; K : Positive) return Boolean is
     (M /= null and then (M.Key = K or else Model_Contains (M.Next, K)));

   function Model_Value (M : access constant Map; K : Positive) return Integer is
     (if M.Key = K then M.Value.all else Model_Value (M.Next, K));
end My_Map;
