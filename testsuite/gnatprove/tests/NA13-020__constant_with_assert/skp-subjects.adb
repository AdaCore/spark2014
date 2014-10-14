package body Skp.Subjects
is

   type Trap_Table_Type is array (Trap_Range) of Trap_Entry_Type;

   Null_Trap_Table : constant Trap_Table_Type := Trap_Table_Type'
     (others => Null_Trap);

   type Event_Table_Type is array (Event_Range) of Event_Entry_Type;

   Null_Event_Table : constant Event_Table_Type := Event_Table_Type'
     (others => Null_Event);

   type Subject_Spec_Type is record
      CPU_Id             : Skp.CPU_Range;
      Profile            : Profile_Kind;
      PML4_Address       : SK.Word64;
      EPT_Pointer        : SK.Word64;
      VMCS_Address       : SK.Word64;
      IO_Bitmap_Address  : SK.Word64;
      MSR_Bitmap_Address : SK.Word64;
      MSR_Store_Address  : SK.Word64;
      Stack_Address      : SK.Word64;
      Entry_Point        : SK.Word64;
      CR0_Value          : SK.Word64;
      CR0_Mask           : SK.Word64;
      CR4_Value          : SK.Word64;
      CR4_Mask           : SK.Word64;
      CS_Access          : SK.Word32;
      Exception_Bitmap   : SK.Word32;
      MSR_Count          : SK.Word32;
      VMX_Controls       : VMX_Controls_Type;
      Trap_Table         : Trap_Table_Type;
      Event_Table        : Event_Table_Type;
   end record;

   type Subject_Spec_Array is array (Skp.Subject_Id_Type) of Subject_Spec_Type;

   Subject_Specs : constant Subject_Spec_Array := Subject_Spec_Array'(
      0 => Subject_Spec_Type'(
       CPU_Id             => 0,
       Profile            => Native,
       PML4_Address       => 16#00f4_a000#,
       EPT_Pointer        => 0,
       VMCS_Address       => 16#5000#,
       IO_Bitmap_Address  => 16#00f6_0000#,
       MSR_Bitmap_Address => 16#00f7_2000#,
       MSR_Store_Address  => 16#0000#,
       Stack_Address      => 16#3000#,
       Entry_Point        => 16#6000#,
       CR0_Value          => 16#8001_0033#,
       CR0_Mask           => 16#e005_003f#,
       CR4_Value          => 16#2220#,
       CR4_Mask           => 16#0017_67ff#,
       CS_Access          => 16#a09b#,
       Exception_Bitmap   => 16#ffff_ffff#,
       MSR_Count          => 0,
       VMX_Controls       => VMX_Controls_Type'(
          Exec_Pin    => 73,
          Exec_Proc   => 2996411904,
          Exec_Proc2  => 64,
          Exit_Ctrls  => 4227584,
          Entry_Ctrls => 512),
       Trap_Table         => Null_Trap_Table,
       Event_Table        => Null_Event_Table),
      1 => Subject_Spec_Type'(
       CPU_Id             => 0,
       Profile            => Native,
       PML4_Address       => 16#00f5_6000#,
       EPT_Pointer        => 0,
       VMCS_Address       => 16#6000#,
       IO_Bitmap_Address  => 16#00f6_a000#,
       MSR_Bitmap_Address => 16#00f7_e000#,
       MSR_Store_Address  => 16#0000#,
       Stack_Address      => 16#3000#,
       Entry_Point        => 16#6000#,
       CR0_Value          => 16#8001_0033#,
       CR0_Mask           => 16#e005_003f#,
       CR4_Value          => 16#2220#,
       CR4_Mask           => 16#0017_67ff#,
       CS_Access          => 16#a09b#,
       Exception_Bitmap   => 16#ffff_ffff#,
       MSR_Count          => 0,
       VMX_Controls       => VMX_Controls_Type'(
          Exec_Pin    => 73,
          Exec_Proc   => 2996411904,
          Exec_Proc2  => 64,
          Exit_Ctrls  => 4227584,
          Entry_Ctrls => 512),
       Trap_Table         => Null_Trap_Table,
       Event_Table        => Event_Table_Type'(
          1 => Event_Entry_Type'(
            Dst_Subject => 5,
            Dst_Vector  => 49,
            Handover    => False,
            Send_IPI    => True),
          2 => Event_Entry_Type'(
            Dst_Subject => 6,
            Dst_Vector  => 49,
            Handover    => False,
            Send_IPI    => True),
          others => Null_Event)),
      2 => Subject_Spec_Type'(
       CPU_Id             => 2,
       Profile            => Native,
       PML4_Address       => 16#00f4_e000#,
       EPT_Pointer        => 0,
       VMCS_Address       => 16#7000#,
       IO_Bitmap_Address  => 16#00f6_2000#,
       MSR_Bitmap_Address => 16#00f7_3000#,
       MSR_Store_Address  => 16#0000#,
       Stack_Address      => 16#3000#,
       Entry_Point        => 16#6000#,
       CR0_Value          => 16#8001_0033#,
       CR0_Mask           => 16#e005_003f#,
       CR4_Value          => 16#2220#,
       CR4_Mask           => 16#0017_67ff#,
       CS_Access          => 16#a09b#,
       Exception_Bitmap   => 16#ffff_ffff#,
       MSR_Count          => 0,
       VMX_Controls       => VMX_Controls_Type'(
          Exec_Pin    => 73,
          Exec_Proc   => 2996411904,
          Exec_Proc2  => 64,
          Exit_Ctrls  => 4227584,
          Entry_Ctrls => 512),
       Trap_Table         => Null_Trap_Table,
       Event_Table        => Event_Table_Type'(
          1 => Event_Entry_Type'(
            Dst_Subject => 1,
            Dst_Vector  => 38,
            Handover    => False,
            Send_IPI    => True),
          others => Null_Event)),
      3 => Subject_Spec_Type'(
       CPU_Id             => 1,
       Profile            => Native,
       PML4_Address       => 16#00f4_6000#,
       EPT_Pointer        => 0,
       VMCS_Address       => 16#8000#,
       IO_Bitmap_Address  => 16#00f5_e000#,
       MSR_Bitmap_Address => 16#00f7_1000#,
       MSR_Store_Address  => 16#0000#,
       Stack_Address      => 16#3000#,
       Entry_Point        => 16#6000#,
       CR0_Value          => 16#8001_0033#,
       CR0_Mask           => 16#e005_003f#,
       CR4_Value          => 16#2220#,
       CR4_Mask           => 16#0017_67ff#,
       CS_Access          => 16#a09b#,
       Exception_Bitmap   => 16#ffff_ffff#,
       MSR_Count          => 0,
       VMX_Controls       => VMX_Controls_Type'(
          Exec_Pin    => 73,
          Exec_Proc   => 2996411904,
          Exec_Proc2  => 64,
          Exit_Ctrls  => 4227584,
          Entry_Ctrls => 512),
       Trap_Table         => Null_Trap_Table,
       Event_Table        => Event_Table_Type'(
          4 => Event_Entry_Type'(
            Dst_Subject => 5,
            Dst_Vector  => Skp.Invalid_Vector,
            Handover    => True,
            Send_IPI    => False),
          1 => Event_Entry_Type'(
            Dst_Subject => 1,
            Dst_Vector  => 36,
            Handover    => False,
            Send_IPI    => True),
          others => Null_Event)),
      4 => Subject_Spec_Type'(
       CPU_Id             => 3,
       Profile            => Native,
       PML4_Address       => 16#00f5_2000#,
       EPT_Pointer        => 0,
       VMCS_Address       => 16#9000#,
       IO_Bitmap_Address  => 16#00f6_8000#,
       MSR_Bitmap_Address => 16#00f7_a000#,
       MSR_Store_Address  => 16#0000#,
       Stack_Address      => 16#3000#,
       Entry_Point        => 16#6000#,
       CR0_Value          => 16#8001_0033#,
       CR0_Mask           => 16#e005_003f#,
       CR4_Value          => 16#2220#,
       CR4_Mask           => 16#0017_67ff#,
       CS_Access          => 16#a09b#,
       Exception_Bitmap   => 16#ffff_ffff#,
       MSR_Count          => 0,
       VMX_Controls       => VMX_Controls_Type'(
          Exec_Pin    => 73,
          Exec_Proc   => 2996411904,
          Exec_Proc2  => 64,
          Exit_Ctrls  => 4227584,
          Entry_Ctrls => 512),
       Trap_Table         => Null_Trap_Table,
       Event_Table        => Event_Table_Type'(
          4 => Event_Entry_Type'(
            Dst_Subject => 6,
            Dst_Vector  => Skp.Invalid_Vector,
            Handover    => True,
            Send_IPI    => False),
          1 => Event_Entry_Type'(
            Dst_Subject => 1,
            Dst_Vector  => 37,
            Handover    => False,
            Send_IPI    => True),
          others => Null_Event)),
      5 => Subject_Spec_Type'(
       CPU_Id             => 1,
       Profile            => Vm,
       PML4_Address       => 0,
       EPT_Pointer        => 16#00da_f01e#,
       VMCS_Address       => 16#a000#,
       IO_Bitmap_Address  => 16#00f5_a000#,
       MSR_Bitmap_Address => 16#00f6_f000#,
       MSR_Store_Address  => 16#00f7_0000#,
       Stack_Address      => 16#0000#,
       Entry_Point        => 16#0040_0000#,
       CR0_Value          => 16#0035#,
       CR0_Mask           => 16#0020#,
       CR4_Value          => 16#2020#,
       CR4_Mask           => 16#2000#,
       CS_Access          => 16#c09b#,
       Exception_Bitmap   => 16#fff0_8002#,
       MSR_Count          => 5,
       VMX_Controls       => VMX_Controls_Type'(
          Exec_Pin    => 73,
          Exec_Proc   => 2996313600,
          Exec_Proc2  => 194,
          Exit_Ctrls  => 7373312,
          Entry_Ctrls => 32768),
       Trap_Table         => Trap_Table_Type'(
          0 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          1 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          2 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          3 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          4 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          5 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          6 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          7 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          8 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          9 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          10 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          11 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          12 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          13 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          14 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          15 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          16 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          17 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          18 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          19 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          20 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          21 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          22 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          23 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          24 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          25 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          26 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          27 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          28 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          29 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          30 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          31 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          32 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          33 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          34 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          36 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          37 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          39 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          40 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          41 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          43 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          44 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          45 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          46 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          47 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          48 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          49 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          50 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          51 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          52 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          53 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          54 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          55 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          56 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          57 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          58 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          59 => Trap_Entry_Type'(Dst_Subject => 3, Dst_Vector => 36),
          others => Null_Trap),
       Event_Table        => Event_Table_Type'(
          1 => Event_Entry_Type'(
            Dst_Subject => 1,
            Dst_Vector  => 34,
            Handover    => False,
            Send_IPI    => True),
          others => Null_Event)),
      6 => Subject_Spec_Type'(
       CPU_Id             => 3,
       Profile            => Vm,
       PML4_Address       => 0,
       EPT_Pointer        => 16#009a_001e#,
       VMCS_Address       => 16#b000#,
       IO_Bitmap_Address  => 16#00f6_4000#,
       MSR_Bitmap_Address => 16#00f7_8000#,
       MSR_Store_Address  => 16#00f7_9000#,
       Stack_Address      => 16#0000#,
       Entry_Point        => 16#0040_0000#,
       CR0_Value          => 16#0035#,
       CR0_Mask           => 16#0020#,
       CR4_Value          => 16#2020#,
       CR4_Mask           => 16#2000#,
       CS_Access          => 16#c09b#,
       Exception_Bitmap   => 16#fff0_8002#,
       MSR_Count          => 5,
       VMX_Controls       => VMX_Controls_Type'(
          Exec_Pin    => 73,
          Exec_Proc   => 2996313600,
          Exec_Proc2  => 194,
          Exit_Ctrls  => 7373312,
          Entry_Ctrls => 32768),
       Trap_Table         => Trap_Table_Type'(
          0 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          1 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          2 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          3 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          4 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          5 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          6 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          7 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          8 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          9 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          10 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          11 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          12 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          13 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          14 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          15 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          16 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          17 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          18 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          19 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          20 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          21 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          22 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          23 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          24 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          25 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          26 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          27 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          28 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          29 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          30 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          31 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          32 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          33 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          34 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          36 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          37 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          39 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          40 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          41 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          43 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          44 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          45 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          46 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          47 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          48 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          49 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          50 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          51 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          52 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          53 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          54 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          55 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          56 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          57 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          58 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          59 => Trap_Entry_Type'(Dst_Subject => 4, Dst_Vector => 36),
          others => Null_Trap),
       Event_Table        => Event_Table_Type'(
          1 => Event_Entry_Type'(
            Dst_Subject => 1,
            Dst_Vector  => 35,
            Handover    => False,
            Send_IPI    => True),
          others => Null_Event)));

   -------------------------------------------------------------------------

   function Get_Event
     (Subject_Id : Skp.Subject_Id_Type;
      Event_Nr   : Event_Range)
      return Event_Entry_Type
   is
   begin
      --  Alt-Ergo and CVC4 have different strengths...
      pragma Assert
       (Subject_Specs (0).Event_Table (0).Dst_Subject /= 0);
      pragma Assert
       (Subject_Specs (0).Event_Table (1).Dst_Subject /= 0);

      return Subject_Specs (Subject_Id).Event_Table (Event_Nr);
   end Get_Event;

   -------------------------------------------------------------------------

   function Get_PML4_Address
     (Subject_Id : Skp.Subject_Id_Type)
      return SK.Word64
   with
      Refined_Post => (Get_PML4_Address'Result mod 4096 = 0)
   is
   begin

      -- We need to explain it to cvc4 in tiny baby steps.
      pragma Assert
        (for all Subject in Skp.Subject_Id_Type range 0 .. 0 =>
           (Subject_Specs (Subject).PML4_Address mod 4096 = 0));
      pragma Assert
        (for all Subject in Skp.Subject_Id_Type range 1 .. 1 =>
           (Subject_Specs (Subject).PML4_Address mod 4096 = 0));
      pragma Assert
        (for all Subject in Skp.Subject_Id_Type range 2 .. 2 =>
           (Subject_Specs (Subject).PML4_Address mod 4096 = 0));
      pragma Assert
        (for all Subject in Skp.Subject_Id_Type range 3 .. 3 =>
           (Subject_Specs (Subject).PML4_Address mod 4096 = 0));
      pragma Assert
        (for all Subject in Skp.Subject_Id_Type range 4 .. 4 =>
           (Subject_Specs (Subject).PML4_Address mod 4096 = 0));
      pragma Assert
        (for all Subject in Skp.Subject_Id_Type range 5 .. 5 =>
           (Subject_Specs (Subject).PML4_Address mod 4096 = 0));
      pragma Assert
        (for all Subject in Skp.Subject_Id_Type range 6 .. 6 =>
           (Subject_Specs (Subject).PML4_Address mod 4096 = 0));

      return Subject_Specs (Subject_Id).PML4_Address;
   end Get_PML4_Address;

end Skp.Subjects;
