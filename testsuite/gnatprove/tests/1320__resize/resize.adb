with Ada.Unchecked_Deallocation;

procedure Resize with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type U32 is mod 2 ** 32;

   type Arr is array (U32 range <>) of Integer;

   type Arr_Ptr is access Arr;

   procedure Free is new Ada.Unchecked_Deallocation (Arr, Arr_Ptr);

   Out_of_Space : exception;

   function Logic_Eq (X, Y : Arr_Ptr) return Boolean
   is (if X = null then Y = null else Y /= null and then X.all = Y.all);

   function Deep_Copy (X : Arr_Ptr) return Arr_Ptr
   with
     Import,
     Global => null,
     Ghost  => Static,
     Post   => Logic_Eq (Deep_Copy'Result, X);

   procedure Resize (A : aliased in out Arr_Ptr)
   with
     Exceptional_Cases => (Out_of_Space => True),
     Pre               => A /= null,
     Post              =>
       (Static =>
          (declare

             Old : constant Arr_Ptr := Deep_Copy (A)'Old;
           begin
             A'Length = (if Old'Length = 0 then 1 else Old'Length * 2)
             and then A'First = 0
             and then
               (if Old'Length > 0
                then
                  (for all I in U32 range 0 .. Old'Length - 1 =>
                     A (I) = Old (Old'First + I)))));

   procedure Resize (A : aliased in out Arr_Ptr) is
   begin
      if A'Length >= U32'Modulus / 2 then
         raise Out_of_Space;
      end if;
      declare
         New_Length : constant U32 :=
           (if A'Length = 0 then 1 else A'Length * 2);
         Copy       : Arr_Ptr := new Arr'([0 .. New_Length - 1 => 0]);
      begin
         if A'Length > 0 then
            for I in U32 range 0 .. A'Length - 1 loop
               pragma
                 Loop_Invariant
                   (Copy /= null
                    and then Copy'First = 0
                    and then Copy'Last = New_Length - 1);
               pragma
                 Loop_Invariant
                   ((if I > 0
                     then
                       (for all K in U32 range 0 .. I - 1 =>
                          Copy (K) = A (A'First + K))));
               Copy (I) := A (A'First + I);
            end loop;
         end if;
         Free (A);
         A := Copy;
      end;
   end Resize;

begin
   null;
end Resize;
