procedure Main with SPARK_Mode is

   Not_Found : exception;

   type Int_Array is array (Positive range <>) of Integer;

   --  Intuitively, the flow graphs for the following function and procedure
   --  should look similar and they should cause similar checks, if any.

   function Find (X : Int_Array; V : Integer) return Positive with
     Side_Effects,
     Always_Terminates,
     Exceptional_Cases => (Not_Found => (for all E of X => E /= V)),
     Post => Find'Result in X'Range and then X (Find'Result) = V;

   procedure Find (X : Int_Array; V : Integer; Result : out Positive) with
     Always_Terminates,
     Exceptional_Cases => (Not_Found => (for all E of X => E /= V)),
     Post => Result in X'Range and then X (Result) = V;

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

   procedure Find (X : Int_Array; V : Integer; Result : out Positive) is
   begin
      for I in X'Range loop
         if X (I) = V then
            Result := I;
            return;
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

begin
   null;
end Main;
