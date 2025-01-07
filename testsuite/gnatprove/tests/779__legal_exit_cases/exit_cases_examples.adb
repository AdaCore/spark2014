procedure Exit_Cases_Examples with SPARK_Mode is

   Not_Found : exception;

   type Int_Array is array (Positive range <>) of Integer;

   function Find (X : Int_Array; V : Integer) return Positive with
     Side_Effects,
     Always_Terminates,
     Exit_Cases =>
       ((for all E of X => E /= V) => (Exception_Raised => Not_Found),
        others                     => Normal_Return),
     Post => Find'Result in X'Range and then X (Find'Result) = V;

   function Find (X : Int_Array; V : Integer) return Positive is
   begin
      for I in X'Range loop
         if X (I) = V then
            return I;
         end if;
         pragma Loop_Invariant (for all K in X'First .. I => X (K) /= V);
      end loop;
      raise Not_Found;
   end Find;

   function Find_2 (X : Int_Array; V : Integer) return Natural with
     Contract_Cases =>
       ((for all E of X => E /= V) => Find_2'Result = 0,
        others                     =>
          Find_2'Result in X'Range and then X (Find_2'Result) = V);

   function Find_2 (X : Int_Array; V : Integer) return Natural is
   begin
      return R : Natural do
         R := Find (X, V);
      exception
         when Not_Found =>
            R := 0;
      end return;
   end Find_2;

   procedure Replace
     (X                    : aliased in out Int_Array;
      Old_Value, New_Value : Integer;
      Pos                  : out Positive)
     with
     Always_Terminates,
     Exit_Cases =>
       ((for all E of X => E /= Old_Value) => (Exception_Raised => Not_Found),
        others => Normal_Return),
     Post => Pos in X'Range and X'Old (Pos) = Old_Value and X (Pos) = New_Value,
     Exceptional_Cases => (Not_Found => X = X'Old);

   procedure Replace
     (X                    : aliased in out Int_Array;
      Old_Value, New_Value : Integer;
      Pos                  : out Positive)
   is
   begin
      for I in X'Range loop
         if X (I) = Old_Value then
            Pos := I;
            X (I) := New_Value;
            return;
         end if;
         pragma Loop_Invariant (for all K in X'First .. I => X (K) /= Old_Value);
      end loop;
      raise Not_Found;
   end Replace;

   procedure Replace_2
     (X                    : aliased in out Int_Array;
      Old_Value, New_Value : Integer;
      Pos                  : out Natural)
     with
     Always_Terminates,
     Contract_Cases =>
       ((for all E of X => E /= Old_Value) => X = X'Old and Pos = 0,
        others => Pos in X'Range and X'Old (Pos) = Old_Value and X (Pos) = New_Value);

   procedure Replace_2
     (X                    : aliased in out Int_Array;
      Old_Value, New_Value : Integer;
      Pos                  : out Natural)
   is
   begin
      Replace (X, Old_Value, New_Value, Pos);
   exception
      when Not_Found =>
         Pos := 0;
   end Replace_2;

begin
   null;
end Exit_Cases_Examples;
