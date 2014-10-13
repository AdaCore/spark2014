with SK;
use type SK.Word64;


package Skp.Subjects
is

   type Profile_Kind is (Native, Vm);

   type Trap_Entry_Type is record
      Dst_Subject : Skp.Dst_Subject_Type;
      Dst_Vector  : Skp.Dst_Vector_Range;
   end record;

   Null_Trap : constant Trap_Entry_Type := Trap_Entry_Type'
     (Dst_Subject => Skp.Invalid_Subject,
      Dst_Vector  => Skp.Invalid_Vector);

   type Trap_Range is range 0 .. 59;

   type Event_Entry_Type is record
      Dst_Subject : Skp.Dst_Subject_Type;
      Dst_Vector  : Skp.Dst_Vector_Range;
      Handover    : Boolean;
      Send_IPI    : Boolean;
   end record;

   Null_Event : constant Event_Entry_Type := Event_Entry_Type'
     (Dst_Subject => Skp.Invalid_Subject,
      Dst_Vector  => Skp.Invalid_Vector,
      Handover    => False,
      Send_IPI    => False);

   type Event_Range is range 0 .. 31;

   type VMX_Controls_Type is record
      Exec_Pin    : SK.Word32;
      Exec_Proc   : SK.Word32;
      Exec_Proc2  : SK.Word32;
      Exit_Ctrls  : SK.Word32;
      Entry_Ctrls : SK.Word32;
   end record;

   function Get_PML4_Address
     (Subject_Id : Skp.Subject_Id_Type)
      return SK.Word64
   with
      Global => null,
      Post   => (Get_PML4_Address'Result mod 4096 = 0);

   function Get_Event
     (Subject_Id : Skp.Subject_Id_Type;
      Event_Nr   : Event_Range)
      return Event_Entry_Type
   with
      Global => null,
      Post   => Get_Event'Result.Dst_Subject /= Subject_Id;

end Skp.Subjects;
