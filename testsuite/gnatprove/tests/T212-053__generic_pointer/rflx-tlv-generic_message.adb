package body RFLX.TLV.Generic_Message with
  SPARK_Mode
is

   function Create return Context is
     ((Types.Index'First, Types.Index'First, Types.Bit_Index'First, Types.Bit_Index'First, null, (F_Tag => (State => S_Invalid, Predecessor => F_Initial), others => (State => S_Invalid, Predecessor => F_Final))));

   procedure Initialize (Ctx : out Context; Buffer : in out Types.Bytes_Ptr) is
   begin
      Initialize (Ctx, Buffer, Types.First_Bit_Index (Buffer'First), Types.Last_Bit_Index (Buffer'Last));
   end Initialize;

   procedure Initialize (Ctx : out Context; Buffer : in out Types.Bytes_Ptr; First, Last : Types.Bit_Index) is
      Buffer_First : constant Types.Index := Buffer'First;
      Buffer_Last : constant Types.Index := Buffer'Last;
   begin
      Ctx := (Buffer_First, Buffer_Last, First, Last, Buffer, (F_Tag => (State => S_Invalid, Predecessor => F_Initial), others => (State => S_Invalid, Predecessor => F_Final)));
      Buffer := null;
   end Initialize;

   function Initialized (Ctx : Context) return Boolean is
     (Valid_Next (Ctx, F_Tag)
      and then Available_Space (Ctx, F_Tag) = (Types.Last_Bit_Index (Ctx.Buffer_Last) - Ctx.First + 1)
      and then Invalid (Ctx, F_Tag)
      and then Invalid (Ctx, F_Length)
      and then Invalid (Ctx, F_Value));

   procedure Take_Buffer (Ctx : in out Context; Buffer : out Types.Bytes_Ptr) is
   begin
      Buffer := Ctx.Buffer;
      Ctx.Buffer := null;
   end Take_Buffer;

   function Has_Buffer (Ctx : Context) return Boolean is
     (Ctx.Buffer /= null);

   function Message_Last (Ctx : Context) return Types.Bit_Index is
     ((if Structural_Valid (Ctx.Cursors (F_Tag))
         and Types.Bit_Length (Ctx.Cursors (F_Tag).Value.Tag_Value) = Types.Bit_Length (Convert (Msg_Error)) then
       Ctx.Cursors (F_Tag).Last
    elsif Structural_Valid (Ctx.Cursors (F_Value)) then
       Ctx.Cursors (F_Value).Last
    else
       Types.Unreachable_Bit_Length));

   function Path_Condition (Ctx : Context; Fld : Field) return Boolean is
     ((case Ctx.Cursors (Fld).Predecessor is
         when F_Initial =>
            (case Fld is
                  when F_Tag =>
                     True,
                  when others =>
                     False),
         when F_Tag =>
            (case Fld is
                  when F_Length =>
                     Types.Bit_Length (Ctx.Cursors (F_Tag).Value.Tag_Value) = Types.Bit_Length (Convert (Msg_Data)),
                  when others =>
                     False),
         when F_Length =>
            (case Fld is
                  when F_Value =>
                     True,
                  when others =>
                     False),
         when F_Value | F_Final =>
            False));

   function Field_Condition (Ctx : Context; Val : Field_Dependent_Value) return Boolean is
     ((case Val.Fld is
         when F_Initial =>
            True,
         when F_Tag =>
            Types.Bit_Length (Val.Tag_Value) = Types.Bit_Length (Convert (Msg_Data))
               or Types.Bit_Length (Val.Tag_Value) = Types.Bit_Length (Convert (Msg_Error)),
         when F_Length | F_Value =>
            True,
         when F_Final =>
            False));

   function Field_Length (Ctx : Context; Fld : Field) return Types.Bit_Length is
     ((case Ctx.Cursors (Fld).Predecessor is
         when F_Initial =>
            (case Fld is
                  when F_Tag =>
                     TLV.Tag_Base'Size,
                  when others =>
                     Types.Unreachable_Bit_Length),
         when F_Tag =>
            (case Fld is
                  when F_Length =>
                     TLV.Length'Size,
                  when others =>
                     Types.Unreachable_Bit_Length),
         when F_Length =>
            (case Fld is
                  when F_Value =>
                     Types.Bit_Length (Ctx.Cursors (F_Length).Value.Length_Value) * 8,
                  when others =>
                     Types.Unreachable_Bit_Length),
         when F_Value | F_Final =>
            0));

   function Field_First (Ctx : Context; Fld : Field) return Types.Bit_Index is
     ((case Fld is
         when F_Tag =>
            Ctx.First,
         when F_Length =>
            (if Ctx.Cursors (Fld).Predecessor = F_Tag
                  and Types.Bit_Length (Ctx.Cursors (F_Tag).Value.Tag_Value) = Types.Bit_Length (Convert (Msg_Data)) then
                (Ctx.Cursors (Ctx.Cursors (Fld).Predecessor).Last + 1)
             else
                Types.Unreachable_Bit_Length),
         when F_Value =>
            (if Ctx.Cursors (Fld).Predecessor = F_Length then
                (Ctx.Cursors (Ctx.Cursors (Fld).Predecessor).Last + 1)
             else
                Types.Unreachable_Bit_Length)));

   function Field_Last (Ctx : Context; Fld : Field) return Types.Bit_Index is
     ((Field_First (Ctx, Fld) + Field_Length (Ctx, Fld) - 1));

   function Predecessor (Ctx : Context; Fld : Virtual_Field) return Virtual_Field is
     ((case Fld is
         when F_Initial =>
            F_Initial,
         when others =>
            Ctx.Cursors (Fld).Predecessor));

   function Successor (Ctx : Context; Fld : Field) return Virtual_Field is
     ((case Fld is
         when F_Tag =>
            (if Types.Bit_Length (Ctx.Cursors (F_Tag).Value.Tag_Value) = Types.Bit_Length (Convert (Msg_Data)) then
                F_Length
             elsif Types.Bit_Length (Ctx.Cursors (F_Tag).Value.Tag_Value) = Types.Bit_Length (Convert (Msg_Error)) then
                F_Final
             else
                F_Initial),
         when F_Length =>
            F_Value,
         when F_Value =>
            F_Final))
    with
     Pre =>
       Structural_Valid (Ctx, Fld)
          and Valid_Predecessor (Ctx, Fld);

   function Valid_Predecessor (Ctx : Context; Fld : Virtual_Field) return Boolean is
     ((case Fld is
         when F_Initial =>
            True,
         when F_Tag =>
            Ctx.Cursors (Fld).Predecessor = F_Initial,
         when F_Length =>
            (Valid (Ctx.Cursors (F_Tag))
                 and Ctx.Cursors (Fld).Predecessor = F_Tag),
         when F_Value =>
            (Valid (Ctx.Cursors (F_Length))
                 and Ctx.Cursors (Fld).Predecessor = F_Length),
         when F_Final =>
            (Valid (Ctx.Cursors (F_Tag))
                 and Ctx.Cursors (Fld).Predecessor = F_Tag)
               or (Structural_Valid (Ctx.Cursors (F_Value))
                 and Ctx.Cursors (Fld).Predecessor = F_Value)));

   function Invalid_Successor (Ctx : Context; Fld : Field) return Boolean is
     ((case Fld is
         when F_Tag =>
            Invalid (Ctx.Cursors (F_Length)),
         when F_Length =>
            Invalid (Ctx.Cursors (F_Value)),
         when F_Value =>
            True));

   function Valid_Next (Ctx : Context; Fld : Field) return Boolean is
     (Valid_Predecessor (Ctx, Fld)
      and then Path_Condition (Ctx, Fld));

   function Available_Space (Ctx : Context; Fld : Field) return Types.Bit_Length is
     ((Types.Last_Bit_Index (Ctx.Buffer_Last) - Field_First (Ctx, Fld) + 1));

   procedure Reset_Dependent_Fields (Ctx : in out Context; Fld : Field) with
     Pre =>
       Valid_Next (Ctx, Fld),
     Post =>
       Valid_Next (Ctx, Fld)
          and Invalid (Ctx.Cursors (Fld))
          and Invalid_Successor (Ctx, Fld)
          and Ctx.Buffer_First = Ctx.Buffer_First'Old
          and Ctx.Buffer_Last = Ctx.Buffer_Last'Old
          and Ctx.First = Ctx.First'Old
          and Ctx.Last = Ctx.Last'Old
          and Ctx.Cursors (Fld).Predecessor = Ctx.Cursors (Fld).Predecessor'Old
          and Has_Buffer (Ctx) = Has_Buffer (Ctx)'Old
          and Field_First (Ctx, Fld) = Field_First (Ctx, Fld)'Old
          and Field_Length (Ctx, Fld) = Field_Length (Ctx, Fld)'Old
          and (case Fld is
               when F_Tag =>
                  Invalid (Ctx, F_Tag)
                     and Invalid (Ctx, F_Length)
                     and Invalid (Ctx, F_Value),
               when F_Length =>
                  Ctx.Cursors (F_Tag) = Ctx.Cursors (F_Tag)'Old
                     and Invalid (Ctx, F_Length)
                     and Invalid (Ctx, F_Value),
               when F_Value =>
                  Ctx.Cursors (F_Tag) = Ctx.Cursors (F_Tag)'Old
                     and Ctx.Cursors (F_Length) = Ctx.Cursors (F_Length)'Old
                     and Invalid (Ctx, F_Value))
   is
      First : constant Types.Bit_Length := Field_First (Ctx, Fld) with
        Ghost;
      Length : constant Types.Bit_Length := Field_Length (Ctx, Fld) with
        Ghost;
   begin
      pragma Assert (Field_First (Ctx, Fld) = First
         and Field_Length (Ctx, Fld) = Length);
      case Fld is
         when F_Tag =>
            Ctx.Cursors (F_Value) := (S_Invalid, F_Final);
            Ctx.Cursors (F_Length) := (S_Invalid, F_Final);
            Ctx.Cursors (F_Tag) := (S_Invalid, Ctx.Cursors (F_Tag).Predecessor);
            pragma Assert (Field_First (Ctx, Fld) = First
               and Field_Length (Ctx, Fld) = Length);
         when F_Length =>
            Ctx.Cursors (F_Value) := (S_Invalid, F_Final);
            Ctx.Cursors (F_Length) := (S_Invalid, Ctx.Cursors (F_Length).Predecessor);
            pragma Assert (Field_First (Ctx, Fld) = First
               and Field_Length (Ctx, Fld) = Length);
         when F_Value =>
            Ctx.Cursors (F_Value) := (S_Invalid, Ctx.Cursors (F_Value).Predecessor);
            pragma Assert (Field_First (Ctx, Fld) = First
               and Field_Length (Ctx, Fld) = Length);
      end case;
   end Reset_Dependent_Fields;

   function Sufficient_Buffer_Length (Ctx : Context; Fld : Field) return Boolean is
     (Ctx.Buffer /= null
      and Ctx.First <= Types.Bit_Index'Last / 2
      and Field_First (Ctx, Fld) <= Types.Bit_Index'Last / 2
      and Field_Length (Ctx, Fld) >= 0
      and Field_Length (Ctx, Fld) <= Types.Bit_Length'Last / 2
      and (Field_First (Ctx, Fld) + Field_Length (Ctx, Fld)) <= Types.Bit_Length'Last / 2
      and Ctx.First <= Field_First (Ctx, Fld)
      and Ctx.Last >= Field_Last (Ctx, Fld))
    with
     Pre =>
       Has_Buffer (Ctx)
          and Valid_Next (Ctx, Fld);

   function Composite_Field (Fld : Field) return Boolean is
     ((case Fld is
         when F_Tag | F_Length =>
            False,
         when F_Value =>
            True));

   function Get_Field_Value (Ctx : Context; Fld : Field) return Field_Dependent_Value with
     Pre =>
       Has_Buffer (Ctx)
          and then Valid_Next (Ctx, Fld)
          and then Sufficient_Buffer_Length (Ctx, Fld),
     Post =>
       Get_Field_Value'Result.Fld = Fld
   is
      First : constant Types.Bit_Index := Field_First (Ctx, Fld);
      Last : constant Types.Bit_Index := Field_Last (Ctx, Fld);
      function Buffer_First return Types.Index is
        (Types.Byte_Index (First));
      function Buffer_Last return Types.Index is
        (Types.Byte_Index (Last));
      function Offset return Types.Offset is
        (Types.Offset ((8 - Last mod 8) mod 8));
      function Extract is new Types.Extract (Types.Index, Types.Byte, Types.Bytes, Types.Offset, TLV.Tag_Base);
      function Extract is new Types.Extract (Types.Index, Types.Byte, Types.Bytes, Types.Offset, TLV.Length);
   begin
      return ((case Fld is
            when F_Tag =>
               (Fld => F_Tag, Tag_Value => Extract (Ctx.Buffer.all (Buffer_First .. Buffer_Last), Offset)),
            when F_Length =>
               (Fld => F_Length, Length_Value => Extract (Ctx.Buffer.all (Buffer_First .. Buffer_Last), Offset)),
            when F_Value =>
               (Fld => F_Value)));
   end Get_Field_Value;

   procedure Verify (Ctx : in out Context; Fld : Field) is
      Value : Field_Dependent_Value;
   begin
      if Has_Buffer (Ctx)
         and then Invalid (Ctx.Cursors (Fld))
         and then Valid_Predecessor (Ctx, Fld)
         and then Path_Condition (Ctx, Fld) then
         if Sufficient_Buffer_Length (Ctx, Fld) then
            Value := Get_Field_Value (Ctx, Fld);
            if Valid_Value (Value)
               and Field_Condition (Ctx, Value) then
               if Composite_Field (Fld) then
                  Ctx.Cursors (Fld) := (State => S_Structural_Valid, First => Field_First (Ctx, Fld), Last => Field_Last (Ctx, Fld), Value => Value, Predecessor => Ctx.Cursors (Fld).Predecessor);
               else
                  Ctx.Cursors (Fld) := (State => S_Valid, First => Field_First (Ctx, Fld), Last => Field_Last (Ctx, Fld), Value => Value, Predecessor => Ctx.Cursors (Fld).Predecessor);
               end if;
               pragma Assert ((if Structural_Valid (Ctx.Cursors (F_Tag)) then
                   (Ctx.Cursors (F_Tag).Last - Ctx.Cursors (F_Tag).First + 1) = TLV.Tag_Base'Size
                     and then Ctx.Cursors (F_Tag).Predecessor = F_Initial
                     and then Ctx.Cursors (F_Tag).First = Ctx.First
                     and then (if Structural_Valid (Ctx.Cursors (F_Length))
                          and then Types.Bit_Length (Ctx.Cursors (F_Tag).Value.Tag_Value) = Types.Bit_Length (Convert (Msg_Data)) then
                        (Ctx.Cursors (F_Length).Last - Ctx.Cursors (F_Length).First + 1) = TLV.Length'Size
                          and then Ctx.Cursors (F_Length).Predecessor = F_Tag
                          and then Ctx.Cursors (F_Length).First = (Ctx.Cursors (F_Tag).Last + 1)
                          and then (if Structural_Valid (Ctx.Cursors (F_Value)) then
                             (Ctx.Cursors (F_Value).Last - Ctx.Cursors (F_Value).First + 1) = Types.Bit_Length (Ctx.Cursors (F_Length).Value.Length_Value) * 8
                               and then Ctx.Cursors (F_Value).Predecessor = F_Length
                               and then Ctx.Cursors (F_Value).First = (Ctx.Cursors (F_Length).Last + 1)))));
               if Fld = F_Tag then
                  Ctx.Cursors (Successor (Ctx, Fld)) := (State => S_Invalid, Predecessor => Fld);
               elsif Fld = F_Length then
                  Ctx.Cursors (Successor (Ctx, Fld)) := (State => S_Invalid, Predecessor => Fld);
               elsif Fld = F_Value then
                  Ctx.Cursors (Successor (Ctx, Fld)) := (State => S_Invalid, Predecessor => Fld);
               end if;
            else
               Ctx.Cursors (Fld) := (State => S_Invalid, Predecessor => F_Final);
            end if;
         else
            Ctx.Cursors (Fld) := (State => S_Incomplete, Predecessor => F_Final);
         end if;
      end if;
   end Verify;

   procedure Verify_Message (Ctx : in out Context) is
   begin
      Verify (Ctx, F_Tag);
      Verify (Ctx, F_Length);
      Verify (Ctx, F_Value);
   end Verify_Message;

   function Present (Ctx : Context; Fld : Field) return Boolean is
     (Structural_Valid (Ctx.Cursors (Fld))
      and then Ctx.Cursors (Fld).First < (Ctx.Cursors (Fld).Last + 1));

   function Structural_Valid (Ctx : Context; Fld : Field) return Boolean is
     ((Ctx.Cursors (Fld).State = S_Valid
        or Ctx.Cursors (Fld).State = S_Structural_Valid));

   function Valid (Ctx : Context; Fld : Field) return Boolean is
     (Ctx.Cursors (Fld).State = S_Valid
      and then Ctx.Cursors (Fld).First < (Ctx.Cursors (Fld).Last + 1));

   function Incomplete (Ctx : Context; Fld : Field) return Boolean is
     (Ctx.Cursors (Fld).State = S_Incomplete);

   function Invalid (Ctx : Context; Fld : Field) return Boolean is
     (Ctx.Cursors (Fld).State = S_Invalid
      or Ctx.Cursors (Fld).State = S_Incomplete);

   function Structural_Valid_Message (Ctx : Context) return Boolean is
     (Valid (Ctx, F_Tag)
      and then ((Valid (Ctx, F_Length)
          and then Types.Bit_Length (Ctx.Cursors (F_Tag).Value.Tag_Value) = Types.Bit_Length (Convert (Msg_Data))
          and then Structural_Valid (Ctx, F_Value))
        or Types.Bit_Length (Ctx.Cursors (F_Tag).Value.Tag_Value) = Types.Bit_Length (Convert (Msg_Error))));

   function Valid_Message (Ctx : Context) return Boolean is
     (Valid (Ctx, F_Tag)
      and then ((Valid (Ctx, F_Length)
          and then Types.Bit_Length (Ctx.Cursors (F_Tag).Value.Tag_Value) = Types.Bit_Length (Convert (Msg_Data))
          and then Valid (Ctx, F_Value))
        or Types.Bit_Length (Ctx.Cursors (F_Tag).Value.Tag_Value) = Types.Bit_Length (Convert (Msg_Error))));

   function Incomplete_Message (Ctx : Context) return Boolean is
     (Incomplete (Ctx, F_Tag)
      or Incomplete (Ctx, F_Length)
      or Incomplete (Ctx, F_Value));

   function Get_Tag (Ctx : Context) return TLV.Tag is
     (Convert (Ctx.Cursors (F_Tag).Value.Tag_Value));

   function Get_Length (Ctx : Context) return TLV.Length is
     (Ctx.Cursors (F_Length).Value.Length_Value);

   procedure Get_Value (Ctx : Context) is
      First : constant Types.Index := Types.Byte_Index (Ctx.Cursors (F_Value).First);
      Last : constant Types.Index := Types.Byte_Index (Ctx.Cursors (F_Value).Last);
   begin
      Process_Value (Ctx.Buffer.all (First .. Last));
   end Get_Value;

   procedure Set_Field_Value (Ctx : in out Context; Val : Field_Dependent_Value; Fst, Lst : out Types.Bit_Index) with
     Pre =>
       not Ctx'Constrained
          and then Has_Buffer (Ctx)
          and then Val.Fld in Field'Range
          and then Valid_Next (Ctx, Val.Fld)
          and then Available_Space (Ctx, Val.Fld) >= Field_Length (Ctx, Val.Fld)
          and then (for all F in Field'Range =>
            (if Structural_Valid (Ctx.Cursors (F)) then
             Ctx.Cursors (F).Last <= Field_Last (Ctx, Val.Fld))),
     Post =>
       Has_Buffer (Ctx)
          and Fst = Field_First (Ctx, Val.Fld)
          and Lst = Field_Last (Ctx, Val.Fld)
          and Fst >= Ctx.First
          and Fst <= (Lst + 1)
          and Types.Byte_Index (Lst) <= Ctx.Buffer_Last
          and (for all F in Field'Range =>
            (if Structural_Valid (Ctx.Cursors (F)) then
             Ctx.Cursors (F).Last <= Lst))
          and Ctx.Buffer_First = Ctx.Buffer_First'Old
          and Ctx.Buffer_Last = Ctx.Buffer_Last'Old
          and Ctx.First = Ctx.First'Old
          and Ctx.Cursors = Ctx.Cursors'Old
   is
      First : constant Types.Bit_Index := Field_First (Ctx, Val.Fld);
      Last : constant Types.Bit_Index := Field_Last (Ctx, Val.Fld);
      function Buffer_First return Types.Index is
        (Types.Byte_Index (First));
      function Buffer_Last return Types.Index is
        (Types.Byte_Index (Last));
      function Offset return Types.Offset is
        (Types.Offset ((8 - Last mod 8) mod 8));
      procedure Insert is new Types.Insert (Types.Index, Types.Byte, Types.Bytes, Types.Offset, TLV.Tag_Base);
      procedure Insert is new Types.Insert (Types.Index, Types.Byte, Types.Bytes, Types.Offset, TLV.Length);
   begin
      Fst := First;
      Lst := Last;
      case Val.Fld is
         when F_Initial =>
            null;
         when F_Tag =>
            Insert (Val.Tag_Value, Ctx.Buffer.all (Buffer_First .. Buffer_Last), Offset);
         when F_Length =>
            Insert (Val.Length_Value, Ctx.Buffer.all (Buffer_First .. Buffer_Last), Offset);
         when F_Value | F_Final =>
            null;
      end case;
   end Set_Field_Value;

   procedure Set_Tag (Ctx : in out Context; Val : TLV.Tag) is
      Field_Value : constant Field_Dependent_Value := (F_Tag, Convert (Val));
      First, Last : Types.Bit_Index;
   begin
      Reset_Dependent_Fields (Ctx, F_Tag);
      Set_Field_Value (Ctx, Field_Value, First, Last);
      Ctx := (Ctx.Buffer_First, Ctx.Buffer_Last, Ctx.First, Last, Ctx.Buffer, Ctx.Cursors);
      Ctx.Cursors (F_Tag) := (State => S_Valid, First => First, Last => Last, Value => Field_Value, Predecessor => Ctx.Cursors (F_Tag).Predecessor);
      Ctx.Cursors (Successor (Ctx, F_Tag)) := (State => S_Invalid, Predecessor => F_Tag);
   end Set_Tag;

   procedure Set_Length (Ctx : in out Context; Val : TLV.Length) is
      Field_Value : constant Field_Dependent_Value := (F_Length, Val);
      First, Last : Types.Bit_Index;
   begin
      Reset_Dependent_Fields (Ctx, F_Length);
      Set_Field_Value (Ctx, Field_Value, First, Last);
      Ctx := (Ctx.Buffer_First, Ctx.Buffer_Last, Ctx.First, Last, Ctx.Buffer, Ctx.Cursors);
      Ctx.Cursors (F_Length) := (State => S_Valid, First => First, Last => Last, Value => Field_Value, Predecessor => Ctx.Cursors (F_Length).Predecessor);
      Ctx.Cursors (Successor (Ctx, F_Length)) := (State => S_Invalid, Predecessor => F_Length);
   end Set_Length;

   procedure Set_Value (Ctx : in out Context) is
      First : constant Types.Bit_Index := Field_First (Ctx, F_Value);
      Last : constant Types.Bit_Index := Field_Last (Ctx, F_Value);
      function Buffer_First return Types.Index is
        (Types.Byte_Index (First));
      function Buffer_Last return Types.Index is
        (Types.Byte_Index (Last));
   begin
      Initialize_Value (Ctx);
      Process_Value (Ctx.Buffer.all (Buffer_First .. Buffer_Last));
   end Set_Value;

   procedure Initialize_Value (Ctx : in out Context) is
      First : constant Types.Bit_Index := Field_First (Ctx, F_Value);
      Last : constant Types.Bit_Index := Field_Last (Ctx, F_Value);
   begin
      Reset_Dependent_Fields (Ctx, F_Value);
      Ctx := (Ctx.Buffer_First, Ctx.Buffer_Last, Ctx.First, Last, Ctx.Buffer, Ctx.Cursors);
      pragma Assert ((if Structural_Valid (Ctx.Cursors (F_Tag)) then
          (Ctx.Cursors (F_Tag).Last - Ctx.Cursors (F_Tag).First + 1) = TLV.Tag_Base'Size
            and then Ctx.Cursors (F_Tag).Predecessor = F_Initial
            and then Ctx.Cursors (F_Tag).First = Ctx.First
            and then (if Structural_Valid (Ctx.Cursors (F_Length))
                 and then Types.Bit_Length (Ctx.Cursors (F_Tag).Value.Tag_Value) = Types.Bit_Length (Convert (Msg_Data)) then
               (Ctx.Cursors (F_Length).Last - Ctx.Cursors (F_Length).First + 1) = TLV.Length'Size
                 and then Ctx.Cursors (F_Length).Predecessor = F_Tag
                 and then Ctx.Cursors (F_Length).First = (Ctx.Cursors (F_Tag).Last + 1)
                 and then (if Structural_Valid (Ctx.Cursors (F_Value)) then
                    (Ctx.Cursors (F_Value).Last - Ctx.Cursors (F_Value).First + 1) = Types.Bit_Length (Ctx.Cursors (F_Length).Value.Length_Value) * 8
                      and then Ctx.Cursors (F_Value).Predecessor = F_Length
                      and then Ctx.Cursors (F_Value).First = (Ctx.Cursors (F_Length).Last + 1)))));
      Ctx.Cursors (F_Value) := (State => S_Structural_Valid, First => First, Last => Last, Value => (Fld => F_Value), Predecessor => Ctx.Cursors (F_Value).Predecessor);
      Ctx.Cursors (Successor (Ctx, F_Value)) := (State => S_Invalid, Predecessor => F_Value);
   end Initialize_Value;

end RFLX.TLV.Generic_Message;
