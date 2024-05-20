with SPARK.Big_Integers; use SPARK.Big_Integers;

package Memory_With_Model
  with SPARK_Mode
is
   pragma Unevaluated_Use_Of_Old (Allow);
   function Big (Arg : Integer) return Valid_Big_Integer renames To_Big_Integer;

   type Chunk is private;

   type Str is array (Positive range 1..<>) of Character;

   function Is_Null (C : Chunk) return Boolean with Ghost;
   function Size (C : Chunk) return Natural with Ghost;
   function Model (C : Chunk) return Str with Ghost;

   function Alloc (Siz : Positive) return Chunk
   with
     Post => not Is_Null(Alloc'Result)
       and then Size(Alloc'Result) = Siz;

   procedure Free (C : in out Chunk)
   with
     Post => Is_Null(C);

   procedure Write (C : in out Chunk; From : Positive; Data : String) with
     Pre => not Is_Null(C)
       and then Data'Length /= 0
       and then Big (From - 1) + Big(Data'Length) <= Big(Size(C))
       and then Big (From - 1) + Big(Data'Length) < Big(Integer'Last),
     Post => not Is_Null(C)
       and then Size(C) = Size(C)'Old
       and then Model(C)(1..From-1) = Model(C)'Old(1..From-1)
       and then Model(C)(From..From-1+Data'Length) = Str(Data)
       and then Model(C)(From+Data'Length..Size(C)) = Model(C)'Old(From+Data'Length..Size(C));

   function Read (C : Chunk; From : Positive; To : Natural) return String with
     Pre => not Is_Null(C)
       and then To in From - 1 .. Size(C),
     Post => Read'Result = String(Model(C)(From..To));

private
   type Chunk is access Str
     with Predicate => Chunk = null or else Chunk.all'Length > 0;

   function Model (C : Chunk) return Str is
     (if C = null then "" else C.all);

   function Is_Null (C : Chunk) return Boolean is (C = null);

   function Size (C : Chunk) return Natural is
     (if C = null then 0 else C.all'Length);

   function Read (C : Chunk; From : Positive; To : Natural) return String is
     (String(C.all(From..To)));

end Memory_With_Model;
