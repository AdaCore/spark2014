with RFLX.Generic_Types;

generic
   with package Types is new RFLX.Generic_Types (<>);
package RFLX.TLV.Generic_Message with
  SPARK_Mode
is

   pragma Annotate (GNATprove, Terminating, Generic_Message);

   use type Types.Bytes, Types.Bytes_Ptr, Types.Index, Types.Length, Types.Bit_Index, Types.Bit_Length;

   pragma Compile_Time_Error (Types.Index'First < 1, "Index'First must be greater than 0");

   pragma Compile_Time_Error (Types.Byte'Size /= 8, "Byte must be of size 8");

   type Virtual_Field is (F_Initial, F_Tag, F_Length, F_Value, F_Final);

   subtype Field is Virtual_Field range F_Tag .. F_Value;

   type Field_Cursor is private with
     Default_Initial_Condition =>
       False;

   type Field_Cursors is array (Virtual_Field) of Field_Cursor;

   type Context (Buffer_First, Buffer_Last : Types.Index := Types.Index'First; First, Last : Types.Bit_Index := Types.Bit_Index'First) is private with
     Default_Initial_Condition =>
       False;

   type Field_Dependent_Value (Fld : Virtual_Field := F_Initial) is
      record
         case Fld is
            when F_Initial | F_Value | F_Final =>
               null;
            when F_Tag =>
               Tag_Value : TLV.Tag_Base;
            when F_Length =>
               Length_Value : TLV.Length;
         end case;
      end record;

   function Create return Context;

   procedure Initialize (Ctx : out Context; Buffer : in out Types.Bytes_Ptr) with
     Pre =>
       not Ctx'Constrained
          and then Buffer /= null
          and then Buffer'Length > 0
          and then Buffer'Last <= Types.Index'Last / 2,
     Post =>
       Valid_Context (Ctx)
          and Has_Buffer (Ctx)
          and Buffer = null
          and Ctx.Buffer_First = Types.Bytes_First (Buffer)'Old
          and Ctx.Buffer_Last = Types.Bytes_Last (Buffer)'Old
          and Ctx.First = Types.First_Bit_Index (Ctx.Buffer_First)
          and Initialized (Ctx);

   procedure Initialize (Ctx : out Context; Buffer : in out Types.Bytes_Ptr; First, Last : Types.Bit_Index) with
     Pre =>
       not Ctx'Constrained
          and then Buffer /= null
          and then Buffer'Length > 0
          and then Types.Byte_Index (First) >= Buffer'First
          and then Types.Byte_Index (Last) <= Buffer'Last
          and then First <= Last
          and then Last <= Types.Bit_Index'Last / 2,
     Post =>
       Valid_Context (Ctx)
          and Buffer = null
          and Has_Buffer (Ctx)
          and Ctx.Buffer_First = Types.Bytes_First (Buffer)'Old
          and Ctx.Buffer_Last = Types.Bytes_Last (Buffer)'Old
          and Ctx.First = First
          and Ctx.Last = Last
          and Initialized (Ctx);

   function Initialized (Ctx : Context) return Boolean with
     Ghost;

   procedure Take_Buffer (Ctx : in out Context; Buffer : out Types.Bytes_Ptr) with
     Pre =>
       Valid_Context (Ctx)
          and Has_Buffer (Ctx),
     Post =>
       Valid_Context (Ctx)
          and not Has_Buffer (Ctx)
          and Buffer /= null
          and Ctx.Buffer_First = Buffer'First
          and Ctx.Buffer_Last = Buffer'Last
          and Ctx.Buffer_First = Ctx.Buffer_First'Old
          and Ctx.Buffer_Last = Ctx.Buffer_Last'Old
          and Ctx.First = Ctx.First'Old
          and Ctx.Last = Ctx.Last'Old
          and Cursors (Ctx) = Cursors (Ctx)'Old;

   function Has_Buffer (Ctx : Context) return Boolean with
     Pre =>
       Valid_Context (Ctx);

   function Message_Last (Ctx : Context) return Types.Bit_Index with
     Pre =>
       Valid_Context (Ctx)
          and Structural_Valid_Message (Ctx);

   function Path_Condition (Ctx : Context; Fld : Field) return Boolean with
     Pre =>
       Valid_Context (Ctx)
          and Valid_Predecessor (Ctx, Fld);

   function Field_Condition (Ctx : Context; Val : Field_Dependent_Value) return Boolean with
     Pre =>
       Valid_Context (Ctx)
          and Val.Fld in Field'Range
          and Valid_Predecessor (Ctx, Val.Fld);

   function Field_Length (Ctx : Context; Fld : Field) return Types.Bit_Length with
     Pre =>
       Valid_Context (Ctx)
          and Valid_Next (Ctx, Fld);

   function Field_First (Ctx : Context; Fld : Field) return Types.Bit_Index with
     Pre =>
       Valid_Context (Ctx)
          and Valid_Next (Ctx, Fld);

   function Field_Last (Ctx : Context; Fld : Field) return Types.Bit_Index with
     Pre =>
       Valid_Next (Ctx, Fld);

   function Predecessor (Ctx : Context; Fld : Virtual_Field) return Virtual_Field with
     Pre =>
       Valid_Context (Ctx);

   function Valid_Predecessor (Ctx : Context; Fld : Virtual_Field) return Boolean with
     Pre =>
       Valid_Context (Ctx);

   function Valid_Next (Ctx : Context; Fld : Field) return Boolean with
     Pre =>
       Valid_Context (Ctx);

   function Available_Space (Ctx : Context; Fld : Field) return Types.Bit_Length with
     Pre =>
       Valid_Context (Ctx)
          and Valid_Next (Ctx, Fld);

   procedure Verify (Ctx : in out Context; Fld : Field) with
     Pre =>
       Valid_Context (Ctx),
     Post =>
       Valid_Context (Ctx)
          and Has_Buffer (Ctx) = Has_Buffer (Ctx)'Old
          and Ctx.Buffer_First = Ctx.Buffer_First'Old
          and Ctx.Buffer_Last = Ctx.Buffer_Last'Old
          and Ctx.First = Ctx.First'Old
          and Ctx.Last = Ctx.Last'Old;

   procedure Verify_Message (Ctx : in out Context) with
     Pre =>
       Valid_Context (Ctx),
     Post =>
       Valid_Context (Ctx)
          and Has_Buffer (Ctx) = Has_Buffer (Ctx)'Old
          and Ctx.Buffer_First = Ctx.Buffer_First'Old
          and Ctx.Buffer_Last = Ctx.Buffer_Last'Old
          and Ctx.First = Ctx.First'Old
          and Ctx.Last = Ctx.Last'Old;

   function Present (Ctx : Context; Fld : Field) return Boolean with
     Pre =>
       Valid_Context (Ctx);

   function Structural_Valid (Ctx : Context; Fld : Field) return Boolean with
     Pre =>
       Valid_Context (Ctx);

   function Valid (Ctx : Context; Fld : Field) return Boolean with
     Pre =>
       Valid_Context (Ctx),
     Post =>
       (if Valid'Result then
           Structural_Valid (Ctx, Fld)
             and Present (Ctx, Fld));

   function Incomplete (Ctx : Context; Fld : Field) return Boolean with
     Pre =>
       Valid_Context (Ctx);

   function Invalid (Ctx : Context; Fld : Field) return Boolean with
     Pre =>
       Valid_Context (Ctx);

   function Structural_Valid_Message (Ctx : Context) return Boolean with
     Pre =>
       Valid_Context (Ctx);

   function Valid_Message (Ctx : Context) return Boolean with
     Pre =>
       Valid_Context (Ctx);

   function Incomplete_Message (Ctx : Context) return Boolean with
     Pre =>
       Valid_Context (Ctx);

   function Get_Tag (Ctx : Context) return TLV.Tag with
     Pre =>
       Valid_Context (Ctx)
          and Valid (Ctx, F_Tag);

   function Get_Length (Ctx : Context) return TLV.Length with
     Pre =>
       Valid_Context (Ctx)
          and Valid (Ctx, F_Length);

   generic
      with procedure Process_Value (Value : Types.Bytes);
   procedure Get_Value (Ctx : Context) with
     Pre =>
       Valid_Context (Ctx)
          and Has_Buffer (Ctx)
          and Present (Ctx, F_Value);

   procedure Set_Tag (Ctx : in out Context; Val : TLV.Tag) with
     Pre =>
       Valid_Context (Ctx)
          and then not Ctx'Constrained
          and then Has_Buffer (Ctx)
          and then Valid_Next (Ctx, F_Tag)
          and then Field_Last (Ctx, F_Tag) <= Types.Bit_Index'Last / 2
          and then Field_Condition (Ctx, (F_Tag, Convert (Val)))
          and then True
          and then Available_Space (Ctx, F_Tag) >= Field_Length (Ctx, F_Tag),
     Post =>
       Valid_Context (Ctx)
          and Has_Buffer (Ctx)
          and Valid (Ctx, F_Tag)
          and Get_Tag (Ctx) = Val
          and Invalid (Ctx, F_Length)
          and Invalid (Ctx, F_Value)
          and (if Types.Bit_Length (Convert (Get_Tag (Ctx))) = Types.Bit_Length (Convert (Msg_Data)) then
             Predecessor (Ctx, F_Length) = F_Tag
               and Valid_Next (Ctx, F_Length))
          and Ctx.Buffer_First = Ctx.Buffer_First'Old
          and Ctx.Buffer_Last = Ctx.Buffer_Last'Old
          and Ctx.First = Ctx.First'Old
          and Predecessor (Ctx, F_Tag) = Predecessor (Ctx, F_Tag)'Old
          and Valid_Next (Ctx, F_Tag) = Valid_Next (Ctx, F_Tag)'Old;

   procedure Set_Length (Ctx : in out Context; Val : TLV.Length) with
     Pre =>
       Valid_Context (Ctx)
          and then not Ctx'Constrained
          and then Has_Buffer (Ctx)
          and then Valid_Next (Ctx, F_Length)
          and then Field_Last (Ctx, F_Length) <= Types.Bit_Index'Last / 2
          and then Field_Condition (Ctx, (F_Length, Val))
          and then Valid (Val)
          and then Available_Space (Ctx, F_Length) >= Field_Length (Ctx, F_Length),
     Post =>
       Valid_Context (Ctx)
          and Has_Buffer (Ctx)
          and Valid (Ctx, F_Length)
          and Get_Length (Ctx) = Val
          and Invalid (Ctx, F_Value)
          and (Predecessor (Ctx, F_Value) = F_Length
            and Valid_Next (Ctx, F_Value))
          and Ctx.Buffer_First = Ctx.Buffer_First'Old
          and Ctx.Buffer_Last = Ctx.Buffer_Last'Old
          and Ctx.First = Ctx.First'Old
          and Predecessor (Ctx, F_Length) = Predecessor (Ctx, F_Length)'Old
          and Valid_Next (Ctx, F_Length) = Valid_Next (Ctx, F_Length)'Old
          and Get_Tag (Ctx) = Get_Tag (Ctx)'Old
          and Cursor (Ctx, F_Tag) = Cursor (Ctx, F_Tag)'Old;

   generic
      with procedure Process_Value (Value : out Types.Bytes);
   procedure Set_Value (Ctx : in out Context) with
     Pre =>
       Valid_Context (Ctx)
          and then not Ctx'Constrained
          and then Has_Buffer (Ctx)
          and then Valid_Next (Ctx, F_Value)
          and then Field_Last (Ctx, F_Value) <= Types.Bit_Index'Last / 2
          and then Field_Condition (Ctx, (Fld => F_Value))
          and then Available_Space (Ctx, F_Value) >= Field_Length (Ctx, F_Value),
     Post =>
       Valid_Context (Ctx)
          and Has_Buffer (Ctx)
          and Ctx.Buffer_First = Ctx.Buffer_First'Old
          and Ctx.Buffer_Last = Ctx.Buffer_Last'Old
          and Ctx.First = Ctx.First'Old
          and Predecessor (Ctx, F_Value) = Predecessor (Ctx, F_Value)'Old
          and Valid_Next (Ctx, F_Value) = Valid_Next (Ctx, F_Value)'Old
          and Get_Tag (Ctx) = Get_Tag (Ctx)'Old
          and Get_Length (Ctx) = Get_Length (Ctx)'Old
          and Structural_Valid (Ctx, F_Value);

   procedure Initialize_Value (Ctx : in out Context) with
     Pre =>
       Valid_Context (Ctx)
          and then not Ctx'Constrained
          and then Has_Buffer (Ctx)
          and then Valid_Next (Ctx, F_Value)
          and then Field_Last (Ctx, F_Value) <= Types.Bit_Index'Last / 2
          and then Field_Condition (Ctx, (Fld => F_Value))
          and then Available_Space (Ctx, F_Value) >= Field_Length (Ctx, F_Value),
     Post =>
       Valid_Context (Ctx)
          and Has_Buffer (Ctx)
          and Ctx.Buffer_First = Ctx.Buffer_First'Old
          and Ctx.Buffer_Last = Ctx.Buffer_Last'Old
          and Ctx.First = Ctx.First'Old
          and Predecessor (Ctx, F_Value) = Predecessor (Ctx, F_Value)'Old
          and Valid_Next (Ctx, F_Value) = Valid_Next (Ctx, F_Value)'Old
          and Get_Tag (Ctx) = Get_Tag (Ctx)'Old
          and Get_Length (Ctx) = Get_Length (Ctx)'Old
          and Structural_Valid (Ctx, F_Value);

   function Valid_Context (Ctx : Context) return Boolean with
     Annotate =>
       (GNATprove, Inline_For_Proof),
     Ghost;

   function Cursor (Ctx : Context; Fld : Field) return Field_Cursor with
     Annotate =>
       (GNATprove, Inline_For_Proof),
     Ghost;

   function Cursors (Ctx : Context) return Field_Cursors with
     Annotate =>
       (GNATprove, Inline_For_Proof),
     Ghost;

private

   type Cursor_State is (S_Valid, S_Structural_Valid, S_Invalid, S_Incomplete);

   function Valid_Value (Val : Field_Dependent_Value) return Boolean is
     ((case Val.Fld is
         when F_Tag =>
            Valid (Val.Tag_Value),
         when F_Length =>
            Valid (Val.Length_Value),
         when F_Value =>
            True,
         when F_Initial | F_Final =>
            False));

   type Field_Cursor (State : Cursor_State := S_Invalid) is
      record
         Predecessor : Virtual_Field := F_Final;
         case State is
            when S_Valid | S_Structural_Valid =>
               First : Types.Bit_Index := Types.Bit_Index'First;
               Last : Types.Bit_Length := Types.Bit_Length'First;
               Value : Field_Dependent_Value := (Fld => F_Final);
            when S_Invalid | S_Incomplete =>
               null;
         end case;
      end record with
     Dynamic_Predicate =>
       (if State = S_Valid
             or State = S_Structural_Valid then
           Valid_Value (Field_Cursor.Value));

   function Structural_Valid (Cursor : Field_Cursor) return Boolean is
     (Cursor.State = S_Valid
      or Cursor.State = S_Structural_Valid);

   function Valid (Cursor : Field_Cursor) return Boolean is
     (Cursor.State = S_Valid);

   function Invalid (Cursor : Field_Cursor) return Boolean is
     (Cursor.State = S_Invalid
      or Cursor.State = S_Incomplete);

   function Valid_Context (Buffer_First, Buffer_Last : Types.Index; First, Last : Types.Bit_Index; Buffer : access constant Types.Bytes; Cursors : Field_Cursors) return Boolean is
     ((if Buffer /= null then
         Buffer'First = Buffer_First
           and Buffer'Last = Buffer_Last)
      and then Types.Byte_Index (First) >= Buffer_First
      and then Types.Byte_Index (Last) <= Buffer_Last
      and then First <= Last
      and then Last <= Types.Bit_Index'Last / 2
      and then (for all F in Field'First .. Field'Last =>
        (if Structural_Valid (Cursors (F)) then
         Cursors (F).First >= First
           and Cursors (F).Last <= Last
           and Cursors (F).First <= (Cursors (F).Last + 1)
           and Cursors (F).Value.Fld = F))
      and then ((if Structural_Valid (Cursors (F_Length)) then
           (Valid (Cursors (F_Tag))
               and then Cursors (F_Length).Predecessor = F_Tag
               and then Types.Bit_Length (Cursors (F_Tag).Value.Tag_Value) = Types.Bit_Length (Convert (Msg_Data))))
        and then (if Structural_Valid (Cursors (F_Value)) then
           (Valid (Cursors (F_Length))
               and then Cursors (F_Value).Predecessor = F_Length)))
      and then ((if Invalid (Cursors (F_Tag)) then
           Invalid (Cursors (F_Length)))
        and then (if Invalid (Cursors (F_Length)) then
           Invalid (Cursors (F_Value))))
      and then (if Structural_Valid (Cursors (F_Tag)) then
         (Cursors (F_Tag).Last - Cursors (F_Tag).First + 1) = TLV.Tag_Base'Size
           and then Cursors (F_Tag).Predecessor = F_Initial
           and then Cursors (F_Tag).First = First
           and then (if Structural_Valid (Cursors (F_Length))
                and then Types.Bit_Length (Cursors (F_Tag).Value.Tag_Value) = Types.Bit_Length (Convert (Msg_Data)) then
              (Cursors (F_Length).Last - Cursors (F_Length).First + 1) = TLV.Length'Size
                and then Cursors (F_Length).Predecessor = F_Tag
                and then Cursors (F_Length).First = (Cursors (F_Tag).Last + 1)
                and then (if Structural_Valid (Cursors (F_Value)) then
                   (Cursors (F_Value).Last - Cursors (F_Value).First + 1) = Types.Bit_Length (Cursors (F_Length).Value.Length_Value) * 8
                     and then Cursors (F_Value).Predecessor = F_Length
                     and then Cursors (F_Value).First = (Cursors (F_Length).Last + 1)))));

   type Context (Buffer_First, Buffer_Last : Types.Index := Types.Index'First; First, Last : Types.Bit_Index := Types.Bit_Index'First) is
      record
         Buffer : Types.Bytes_Ptr := null;
         Cursors : Field_Cursors := (others => (State => S_Invalid, Predecessor => F_Final));
      end record with
     Dynamic_Predicate =>
       Valid_Context (Buffer_First, Buffer_Last, First, Last, Buffer, Cursors);

   function Valid_Context (Ctx : Context) return Boolean is
     (Valid_Context (Ctx.Buffer_First, Ctx.Buffer_Last, Ctx.First, Ctx.Last, Ctx.Buffer, Ctx.Cursors));

   function Cursor (Ctx : Context; Fld : Field) return Field_Cursor is
     (Ctx.Cursors (Fld));

   function Cursors (Ctx : Context) return Field_Cursors is
     (Ctx.Cursors);

end RFLX.TLV.Generic_Message;
