package My_Map with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Map is private with
     Iterable =>
       (First       => First,
        Next        => Next,
        Has_Element => Has_Element,
        Element     => Element);
   type Map_Acc is access Map;

   function Model_Contains (M : access constant Map; K : Positive) return Boolean
   with
     Ghost,
     Annotate => (GNATprove, Terminating);

   function Model_Value (M : access constant Map; K : Positive) return Integer
   with
     Ghost,
     Annotate => (GNATprove, Terminating),
     Pre => Model_Contains (M, K);

   function Pledge (Borrower : access constant Map; Prop : Boolean) return Boolean is
     (Prop)
   with Ghost,
     Annotate => (GNATprove, Pledge);

   function Pledge (Borrower : access constant Integer; Prop : Boolean) return Boolean is
     (Prop)
   with Ghost,
     Annotate => (GNATprove, Pledge);

   function Contains (M : access constant Map; K : Positive) return Boolean with
     Post => Contains'Result = Model_Contains (M, K);

   procedure Replace_Element (M : access Map; K : Positive; V : Integer) with
     Pre  => Model_Contains (M, K),
     Post => Model_Contains (M, K) and then Model_Value (M, K) = V;

   procedure Replace_Element_Ext (M : access Map; K : Positive; V : Integer) with
     Pre  => Model_Contains (M, K),
     Post => Model_Contains (M, K) and then Model_Value (M, K) = V
         and then
          (declare
             Old_M : constant Map_Acc := Deep_Copy (M)'Old;
           begin
             (for all K in Map_Acc'(Old_M).all => Model_Contains (M, K))
               and then (for all L in M.all => Model_Contains (Old_M, L)
                         and then (if L /= K then Model_Value (M, L) = Model_Value (Old_M, L))));

   function Constant_Access (M : access constant Map; K : Positive) return not null access constant Integer with
     Pre  => Model_Contains (M, K),
     Post => Model_Value (M, K) = Constant_Access'Result.all;

   function Reference (M : access Map; K : Positive) return not null access Integer with
     Pre  => Model_Contains (M, K),
     Post => Model_Value (M, K) = Reference'Result.all and then
     Pledge (Reference'Result, Model_Contains (M, K) and then
                 Model_Value (M, K) = Reference'Result.all);

   --  For quantification purpose only, inefficient

   function First (M : Map) return Natural with
     Ghost,
     Annotate => (GNATprove, Terminating);
   function Has_Element (M : Map; K : Natural) return Boolean with
     Ghost,
     Annotate => (GNATprove, Terminating);
   function Next (M : Map; K : Natural) return Natural with
     Ghost,
     Annotate => (GNATprove, Terminating),
     Pre => Has_Element (M, K);
   function Element (M : Map; K : Natural) return Integer with
     Ghost,
     Annotate => (GNATprove, Terminating),
     Pre      => Has_Element (M, K);

   function Deep_Copy (M : access constant Map) return Map_Acc with
     Ghost,
     Annotate => (GNATprove, Terminating),
     Post => (Deep_Copy'Result = null) = (M = null)
     and then
       (if M /= null then
          (for all K in M.all => Model_Contains (Deep_Copy'Result, K))
        and then
          (for all K in Deep_Copy'Result.all => Model_Contains (M, K)
           and then Model_Value (M, K) = Model_Value (Deep_Copy'Result, K)));

   procedure Deep_Free (M : in out Map_Acc) with
     Post => M = null;

private
   type Nullable_Int_Acc is access Integer;
   subtype Int_Acc is not null Nullable_Int_Acc;
   type Map is record
      Key   : Positive;
      Value : Int_Acc;
      Next  : Map_Acc;
   end record;

   function Model_Contains (M : access constant Map; K : Positive) return Boolean is
     (M /= null and then Has_Element (M.all, K));

   function Model_Value (M : access constant Map; K : Positive) return Integer is
     (if M.Key = K then M.Value.all else Model_Value (M.Next, K));

   function First (M : Map) return Natural is
      (M.Key);
   function Has_Element (M : Map; K : Natural) return Boolean is
     (K /= 0 and then
        (M.Key = K or else Model_Contains (M.Next, K)));
   function Next (M : Map; K : Natural) return Natural is
     (if M.Key /= K then Next (M.Next.all, K)
      elsif M.Next = null then 0
      else M.Next.Key);
   function Element (M : Map; K : Natural) return Integer is
     (if M.Key = K then M.Value.all else Model_Value (M.Next, K));
end My_Map;
