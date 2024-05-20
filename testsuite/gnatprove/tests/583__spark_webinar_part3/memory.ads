with SPARK.Big_Integers; use SPARK.Big_Integers;

package Memory
  with SPARK_Mode
is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Chunk is private;

   function Is_Null (C : Chunk) return Boolean with Ghost;
   function Size (C : Chunk) return Natural with Ghost;

   function Is_Initialized (C : Chunk; From : Positive; To : Natural) return Boolean
   with
     Ghost,
     Pre => not Is_Null(C) and then To in From - 1 .. Size(C);

   function Big (Arg : Integer) return Valid_Big_Integer renames To_Big_Integer;

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
       and then Is_Initialized(C, 1, From - 1),
     Post => not Is_Null(C)
       and then Size(C) = Size(C)'Old
       and then Is_Initialized(C, 1, From - 1 + Data'Length)
       and then Read(C, 1, From - 1) = Read(C, 1, From - 1)'Old
       and then Read(C, From, From - 1 + Data'Length) = Data;

   function Read (C : Chunk; From : Positive; To : Natural) return String with
     Pre => not Is_Null(C)
       and then To in From - 1 .. Size(C)
       and then Is_Initialized(C, From, To);

private
   type Str is new String(1..<>)
     with Relaxed_Initialization;

   type Chunk is access Str
     with Predicate => Chunk = null or else Chunk.all'Length > 0;

   function Is_Null (C : Chunk) return Boolean is (C = null);

   function Size (C : Chunk) return Natural is
     (if C = null then 0 else C.all'Length);

   function Is_Initialized (C : Chunk; From : Positive; To : Natural) return Boolean is
      (C.all(From..To)'Initialized);

   function Read (C : Chunk; From : Positive; To : Natural) return String is
     (String(C.all(From..To)));

end Memory;
