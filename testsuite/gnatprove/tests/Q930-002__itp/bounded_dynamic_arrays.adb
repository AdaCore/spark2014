package body Bounded_Dynamic_Arrays is

   -----------
   -- Clear --
   -----------

   procedure Clear (This : out Sequence) is
   begin
      This.Current_Length := 0;
      This.Content := (others => Default_Value);
   end Clear;

   -------------------
   -- Null_Sequence --
   -------------------

   function Null_Sequence return Sequence is
      Result : Sequence (Capacity => 0);
   begin
      Result.Current_Length := 0;
      Result.Content (1 .. 0) := Null_List;
      return Result;
   end Null_Sequence;

   --------------
   -- Instance --
   --------------

   function Instance (Capacity : Natural_Index; Content : List) return Sequence is
      Result : Sequence (Capacity);
   begin
      Result.Current_Length := Content'Length;
      Result.Content (1 .. Result.Current_Length) := Content;
      return Result;
   end Instance;

   --------------
   -- Instance --
   --------------

   function Instance (Content : List) return Sequence is
   begin
      return Instance (Capacity => Content'Length, Content => Content);
   end Instance;

   --------------
   -- Instance --
   --------------

   function Instance (Capacity : Natural_Index; C : Component) return Sequence is
      Result : Sequence (Capacity);
   begin
      Result.Current_Length := 1;
      Result.Content (1) := C;
      return Result;
   end Instance;

   ---------
   -- "&" --
   ---------

   function "&" (Left : Sequence; Right : Sequence) return Sequence is
   begin
      return Instance
        (Capacity => Left.Current_Length + Right.Current_Length,
         Content  => Value (Left) & Value (Right));
   end "&";

   ---------
   -- "&" --
   ---------

   function "&" (Left : Sequence; Right : List) return Sequence is
   begin
      return Instance
        (Capacity => Left.Current_Length + Right'Length,
         Content  => Value (Left) & Right);
   end "&";

   ---------
   -- "&" --
   ---------

   function "&" (Left : List; Right : Sequence) return Sequence is
   begin
      return Instance
        (Capacity => Left'Length + Right.Current_Length,
         Content  => Left & Value (Right));
   end "&";

   ---------
   -- "&" --
   ---------

   function "&" (Left : Sequence; Right : Component) return Sequence is
   begin
      return Instance
        (Capacity => Left.Current_Length + 1,
         Content  => Value (Left) & Right);
   end "&";

   ---------
   -- "&" --
   ---------

   function "&" (Left : Component; Right : Sequence) return Sequence is
   begin
      return Instance
        (Capacity => Right.Current_Length + 1,
         Content  => Left & Value (Right));
   end "&";

   ----------
   -- Copy --
   ----------

   procedure Copy (Source : Sequence; To : in out Sequence) is
      subtype Current_Range is Index range 1 .. Source.Current_Length;
   begin
      To.Content (Current_Range) := Source.Content (Current_Range);
      To.Current_Length := Source.Current_Length;
   end Copy;

   ----------
   -- Copy --
   ----------

   procedure Copy (Source : List; To : in out Sequence) is
   begin
      To.Current_Length := Source'Length;
      To.Content (1 .. Source'Length) := Source;
   end Copy;

   ----------
   -- Copy --
   ----------

   procedure Copy (Source : Component; To : in out Sequence) is
   begin
      To.Content (1) := Source;
      To.Current_Length := 1;
   end Copy;

   ------------
   -- Append --
   ------------

   procedure Append (Tail : Sequence; To : in out Sequence) is
      New_Length : constant Index := Length (Tail) + To.Current_Length;
   begin
      To.Content (1 .. New_Length) := Value (To) & Value (Tail);
      To.Current_Length := New_Length;
   end Append;

   ------------
   -- Append --
   ------------

   procedure Append (Tail : List; To : in out Sequence) is
      New_Length : constant Index := Tail'Length + To.Current_Length;
   begin
      To.Content (1 .. New_Length) := Value (To) & Tail;
      To.Current_Length := New_Length;
   end Append;

   ------------
   -- Append --
   ------------

   procedure Append (Tail : Component; To : in out Sequence) is
      New_Length : constant Index := 1 + To.Current_Length;
   begin
      To.Content (New_Length) := Tail;
      To.Current_Length := New_Length;
   end Append;

   ------------
   -- Ammend --
   ------------

   procedure Ammend (This : in out Sequence; By : Sequence; Start : Index) is
   begin
      Ammend (This, Value (By), Start);
   end Ammend;

   ------------
   -- Ammend --
   ------------

   procedure Ammend (This : in out Sequence; By : List; Start : Index) is
      Last : constant Index := Start + By'Length - 1;
   begin
      This.Content (Start .. Last) := By;
      if Last > This.Current_Length then
         This.Current_Length := Last;
      end if;
   end Ammend;

   ------------
   -- Ammend --
   ------------

   procedure Ammend (This : in out Sequence; By : Component; Start : Index) is
   begin
      This.Content (Start) := By;
   end Ammend;

   --------------
   -- Location --
   --------------

   function Location (Fragment : Sequence; Within : Sequence) return Natural_Index is
   begin
      return Location (Value (Fragment), Within);
   end Location;

   --------------
   -- Location --
   --------------

   function Location (Fragment : List; Within : Sequence) return Natural_Index is
   begin
      --  We must check for the empty Fragment since that would be found, but
      --  we want to return zero (indicating not found) in that case. It would
      --  be found because on the first iteration with K = 1, the condition in
      --  the if-statement would be computing a null slice on the LHS of the
      --  comparison (ie, the range would be 1 .. 1+0-1), and that LHS would
      --  equal the RHS empty array fragment. We must also check for the
      --  fragment not being longer than the content of Within itself.
      if Fragment'Length in 1 .. Within.Current_Length then
         for K in 1 .. (Within.Current_Length - Fragment'Length + 1) loop
            if Within.Content (K .. (K + Fragment'Length - 1)) = Fragment then
               return K;
            end if;
            pragma Loop_Invariant
              ((for all J in 1 .. K =>
                 Within.Content (J .. (J + Fragment'Length - 1)) /= Fragment));
         end loop;
      end if;
      pragma Assert (not Contains (Within, Fragment));
      return 0;
   end Location;

   --------------
   -- Location --
   --------------

   function Location (Fragment : Component; Within : Sequence) return Natural_Index is
   begin
      for K in 1 .. Within.Current_Length loop
         if Within.Content (K) = Fragment then
            return K;
         end if;
         pragma Loop_Invariant ((for all J in 1 .. K => Within.Content (J) /= Fragment));
      end loop;
      return 0;
   end Location;

end Bounded_Dynamic_Arrays;
