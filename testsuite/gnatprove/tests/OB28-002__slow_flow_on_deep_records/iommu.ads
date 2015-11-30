with Interfaces;

with SK;

package IOMMU
with
   SPARK_Mode,
   Abstract_State =>
     (State with External => (Async_Writers, Async_Readers, Effective_Writes)),
   Initializes    => State
is

   Root_Table_Address    : constant := 16#00f8_8000#;
   Base_Address          : constant := 16#0020_1000#;

   IR_Table_Phys_Address : constant := 16#0f87#;
   IR_Table_Virt_Address : constant := 16#001f_e000#;
   IR_Table_Size         : constant := 7;

   Cap_AGAW_Bit          : constant := 2;

   type IOMMU_Device_Range is range 1 .. 2;

   --  Basic types

   type Bit_Type is mod 2 ** 1
     with
       Size => 1;

   type Bit_Array is array (Positive range <>) of Bit_Type
     with
       Pack;

   type Bit_2_Type is mod 2 ** 2
     with
       Size => 2;

   type Bit_3_Type is mod 2 ** 3
     with
       Size => 3;

   type Bit_4_Type is mod 2 ** 4
     with
       Size => 4;

   type Bit_10_Type is mod 2 ** 10
     with
       Size => 10;

   type Bit_52_Type is mod 2 ** 52
     with
       Size => 52;

   --  Registers

   --  Version register
   type Reg_Version_Type is record
      MIN      : Bit_4_Type;
      MAX      : Bit_4_Type;
      Reserved : Bit_Array (1 .. 24);
   end record
     with
       Size => 32;

   for Reg_Version_Type use record
      MIN      at 0 range 0 ..  3;
      MAX      at 0 range 4 ..  7;
      Reserved at 0 range 8 .. 31;
   end record;

   --  Capability register
   type Reg_Capability_Type is record
      ND         : Bit_3_Type;
      AFL        : Bit_Type;
      RWBF       : Bit_Type;
      PLMR       : Bit_Type;
      PHMR       : Bit_Type;
      CM         : Bit_Type;
      SAGAW      : Bit_Array (1 .. 5);
      Reserved_1 : Bit_Array (1 .. 3);
      MGAW       : Bit_Array (1 .. 6);
      ZLR        : Bit_Type;
      Reserved_2 : Bit_Type;
      FRO        : Bit_10_Type;
      SLLPS      : Bit_Array (1 .. 4);
      Reserved_3 : Bit_Type;
      PSI        : Bit_Type;
      NFR        : SK.Byte;
      MAMV       : Bit_Array (1 .. 6);
      DWD        : Bit_Type;
      DRD        : Bit_Type;
      FL1GP      : Bit_Type;
      Reserved_4 : Bit_Array (1 .. 7);
   end record
     with Size => 64;

   for Reg_Capability_Type use record
      ND         at 0 range 0  .. 2;
      AFL        at 0 range 3  .. 3;
      RWBF       at 0 range 4  .. 4;
      PLMR       at 0 range 5  .. 5;
      PHMR       at 0 range 6  .. 6;
      CM         at 0 range 7  .. 7;
      SAGAW      at 0 range 8  .. 12;
      Reserved_1 at 0 range 13 .. 15;
      MGAW       at 0 range 16 .. 21;
      ZLR        at 0 range 22 .. 22;
      Reserved_2 at 0 range 23 .. 23;
      FRO        at 0 range 24 .. 33;
      SLLPS      at 0 range 34 .. 37;
      Reserved_3 at 0 range 38 .. 38;
      PSI        at 0 range 39 .. 39;
      NFR        at 0 range 40 .. 47;
      MAMV       at 0 range 48 .. 53;
      DWD        at 0 range 54 .. 54;
      DRD        at 0 range 55 .. 55;
      FL1GP      at 0 range 56 .. 56;
      Reserved_4 at 0 range 57 .. 63;
   end record;

   --  Extended Capability register
   type Reg_Extcapability_Type is record
      C          : Bit_Type;
      QI         : Bit_Type;
      DT         : Bit_Type;
      IR         : Bit_Type;
      EIM        : Bit_Type;
      Reserved_1 : Bit_Type;
      PT         : Bit_Type;
      SC         : Bit_Type;
      IRO        : Bit_10_Type;
      Reserved_2 : Bit_Array (1 .. 2);
      MHMV       : Bit_Array (1 .. 4);
      ECS        : Bit_Type;
      MTS        : Bit_Type;
      NEST       : Bit_Type;
      DIS        : Bit_Type;
      PASID      : Bit_Type;
      PRS        : Bit_Type;
      ERS        : Bit_Type;
      SRS        : Bit_Type;
      POT        : Bit_Type;
      NWFS       : Bit_Type;
      EAFS       : Bit_Type;
      PSS        : Bit_Array (1 .. 5);
      Reserved_3 : Bit_Array (1 .. 24);
   end record;

   for Reg_Extcapability_Type use record
      C          at 0 range 0  .. 0;
      QI         at 0 range 1  .. 1;
      DT         at 0 range 2  .. 2;
      IR         at 0 range 3  .. 3;
      EIM        at 0 range 4  .. 4;
      Reserved_1 at 0 range 5  .. 5;
      PT         at 0 range 6  .. 6;
      SC         at 0 range 7  .. 7;
      IRO        at 0 range 8  .. 17;
      Reserved_2 at 0 range 18 .. 19;
      MHMV       at 0 range 20 .. 23;
      ECS        at 0 range 24 .. 24;
      MTS        at 0 range 25 .. 25;
      NEST       at 0 range 26 .. 26;
      DIS        at 0 range 27 .. 27;
      PASID      at 0 range 28 .. 28;
      PRS        at 0 range 29 .. 29;
      ERS        at 0 range 30 .. 30;
      SRS        at 0 range 31 .. 31;
      POT        at 0 range 32 .. 32;
      NWFS       at 0 range 33 .. 33;
      EAFS       at 0 range 34 .. 34;
      PSS        at 0 range 35 .. 39;
      Reserved_3 at 0 range 40 .. 63;
   end record;

   --  Global Command Register
   type Reg_Global_Command_Type is record
      Reserved : Bit_Array (1 .. 23);
      CFI      : Bit_Type;
      SIRTP    : Bit_Type;
      IRE      : Bit_Type;
      QIE      : Bit_Type;
      WBF      : Bit_Type;
      EAFL     : Bit_Type;
      SFL      : Bit_Type;
      SRTP     : Bit_Type;
      TE       : Bit_Type;
   end record
     with
       Size => 32;

   for Reg_Global_Command_Type use record
      Reserved at 0 range 0  .. 22;
      CFI      at 0 range 23 .. 23;
      SIRTP    at 0 range 24 .. 24;
      IRE      at 0 range 25 .. 25;
      QIE      at 0 range 26 .. 26;
      WBF      at 0 range 27 .. 27;
      EAFL     at 0 range 28 .. 28;
      SFL      at 0 range 29 .. 29;
      SRTP     at 0 range 30 .. 30;
      TE       at 0 range 31 .. 31;
   end record;

   --  Global Status Register
   type Reg_Global_Status_Type is record
      Reserved : Bit_Array (1 .. 23);
      CFIS     : Bit_Type;
      IRTPS    : Bit_Type;
      IRES     : Bit_Type;
      QIES     : Bit_Type;
      WBFS     : Bit_Type;
      AFLS     : Bit_Type;
      FLS      : Bit_Type;
      RTPS     : Bit_Type;
      TES      : Bit_Type;
   end record
     with
       Size => 32;

   for Reg_Global_Status_Type use record
      Reserved at 0 range 0  .. 22;
      CFIS     at 0 range 23 .. 23;
      IRTPS    at 0 range 24 .. 24;
      IRES     at 0 range 25 .. 25;
      QIES     at 0 range 26 .. 26;
      WBFS     at 0 range 27 .. 27;
      AFLS     at 0 range 28 .. 28;
      FLS      at 0 range 29 .. 29;
      RTPS     at 0 range 30 .. 30;
      TES      at 0 range 31 .. 31;
   end record;

   --  Context Command Register
   type Reg_Context_Command_Type is record
      Unused : Bit_Array (1 .. 61);
      CIRG   : Bit_2_Type;
      ICC    : Bit_Type;
   end record
     with
       Size => 64;

   for Reg_Context_Command_Type use record
      Unused at 0 range  0 .. 60;
      CIRG   at 0 range 61 .. 62;
      ICC    at 0 range 63 .. 63;
   end record;

   --  Fault Status Register
   type Reg_Fault_Status_Type is record
      PFO      : Bit_Type;
      PPF      : Bit_Type;
      AFO      : Bit_Type;
      APF      : Bit_Type;
      IQE      : Bit_Type;
      ICE      : Bit_Type;
      ITE      : Bit_Type;
      PRO      : Bit_Type;
      FRI      : SK.Byte;
      Reserved : SK.Word16;
   end record
     with
       Size => 32;

   for Reg_Fault_Status_Type use record
      PFO      at 0 range 0  .. 0;
      PPF      at 0 range 1  .. 1;
      AFO      at 0 range 2  .. 2;
      APF      at 0 range 3  .. 3;
      IQE      at 0 range 4  .. 4;
      ICE      at 0 range 5  .. 5;
      ITE      at 0 range 6  .. 6;
      PRO      at 0 range 7  .. 7;
      FRI      at 0 range 8  .. 15;
      Reserved at 0 range 16 .. 31;
   end record;

   type Reg_Fault_Event_Control_Type is record
      Reserved : Bit_Array (1 .. 30);
      IP       : Bit_Type;
      IM       : Bit_Type;
   end record
     with
       Size => 32;

   for Reg_Fault_Event_Control_Type use record
      Reserved at 0 range 0  .. 29;
      IP       at 0 range 30 .. 30;
      IM       at 0 range 31 .. 31;
   end record;

   type Reg_Fault_Event_Data_Type is record
      IMD  : SK.Word16;
      EIMD : SK.Word16;
   end record
     with
       Size => 32;

   for Reg_Fault_Event_Data_Type use record
      IMD  at 0 range 0  .. 15;
      EIMD at 0 range 16 .. 31;
   end record;

   type Reg_Fault_Event_Address_Type is record
      Reserved_1       : Bit_Array (1 .. 2);
      Destination_Mode : Bit_Type;
      Redirection_Hint : Bit_Type;
      Reserved_2       : SK.Byte;
      APIC_ID          : SK.Byte;
      FEEh             : Bit_Array (1 .. 12);
   end record
     with
       Size => 32;

   for Reg_Fault_Event_Address_Type use record
      Reserved_1       at 0 range 0  .. 1;
      Destination_Mode at 0 range 2  .. 2;
      Redirection_Hint at 0 range 3  .. 3;
      Reserved_2       at 0 range 4  .. 11;
      APIC_ID          at 0 range 12 .. 19;
      FEEh             at 0 range 20 .. 31;
   end record;

   --  Interrupt Remapping Table Address Register
   type Reg_IRT_Address is record
      S        : Bit_4_Type;
      Reserved : Bit_Array (1 .. 7);
      EIME     : Bit_Type;
      IRTA     : Bit_52_Type;
   end record
     with
       Size => 64;

   for Reg_IRT_Address use record
      S        at 0 range  0 .. 3;
      Reserved at 0 range  4 .. 10;
      EIME     at 0 range 11 .. 11;
      IRTA     at 0 range 12 .. 63;
   end record;

   --  IOTLB Invalidate Register (dynamic)
   type Reg_IOTLB_Invalidate is record
      Unused   : Bit_Array (1 .. 60);
      IIRG     : Bit_2_Type;
      Reserved : Bit_Type;
      IVT      : Bit_Type;
   end record;

   for Reg_IOTLB_Invalidate use record
      Unused   at 0 range 0  .. 59;
      IIRG     at 0 range 60 .. 61;
      Reserved at 0 range 62 .. 62;
      IVT      at 0 range 63 .. 63;
   end record;

   --  Fault Recording Register (dynamic)
   type Reg_Fault_Recording_Type is record
      Reserved_1 : Bit_Array (1 .. 12);
      FI         : Bit_52_Type;
      SID        : SK.Word16;
      Reserved_2 : Bit_Array (1 .. 13);
      PRIV       : Bit_Type;
      EXE        : Bit_Type;
      PP         : Bit_Type;
      FR         : SK.Byte;
      PV         : Bit_Array (1 .. 20);
      AType      : Bit_2_Type;
      T          : Bit_Type;
      F          : Bit_Type;
   end record
     with
       Size => 128;

   for Reg_Fault_Recording_Type use record
      Reserved_1 at 0 range 0   .. 11;
      FI         at 0 range 12  .. 63;
      SID        at 0 range 64  .. 79;
      Reserved_2 at 0 range 80  .. 92;
      PRIV       at 0 range 93  .. 93;
      EXE        at 0 range 94  .. 94;
      PP         at 0 range 95  .. 95;
      FR         at 0 range 96  .. 103;
      PV         at 0 range 104 .. 123;
      AType      at 0 range 124 .. 125;
      T          at 0 range 126 .. 126;
      F          at 0 range 127 .. 127;
   end record;

   function Read_Version
     (Index : IOMMU_Device_Range)
      return Reg_Version_Type;

   function Read_Capability
     (Index : IOMMU_Device_Range)
      return Reg_Capability_Type;

   function Read_Extended_Capability
     (Index : IOMMU_Device_Range)
      return Reg_Extcapability_Type;

   function Read_Global_Status
     (Index : IOMMU_Device_Range)
      return Reg_Global_Status_Type;

   procedure Write_Root_Table_Address
     (Index : IOMMU_Device_Range;
      Value : SK.Word64);

   procedure Write_Global_Command
     (Index : IOMMU_Device_Range;
      Value : Reg_Global_Command_Type);

   function Read_Context_Command
     (Index : IOMMU_Device_Range)
      return Reg_Context_Command_Type;

   procedure Write_Context_Command
     (Index : IOMMU_Device_Range;
      Value : Reg_Context_Command_Type);

   function Read_Fault_Recording
     (Index : IOMMU_Device_Range)
      return Reg_Fault_Recording_Type;

   procedure Write_Fault_Recording
     (Index : IOMMU_Device_Range;
      Value : Reg_Fault_Recording_Type);

   function Read_Fault_Status
     (Index : IOMMU_Device_Range)
      return Reg_Fault_Status_Type;

   procedure Write_Fault_Status
     (Index : IOMMU_Device_Range;
      Value : Reg_Fault_Status_Type);

   function Read_Fault_Event_Control
     (Index : IOMMU_Device_Range)
      return Reg_Fault_Event_Control_Type;

   procedure Write_Fault_Event_Control
     (Index : IOMMU_Device_Range;
      Value : Reg_Fault_Event_Control_Type);

   function Read_Fault_Event_Address
     (Index : IOMMU_Device_Range)
      return Reg_Fault_Event_Address_Type;

   procedure Write_Fault_Event_Address
     (Index : IOMMU_Device_Range;
      Value : Reg_Fault_Event_Address_Type);

   function Read_Fault_Event_Data
     (Index : IOMMU_Device_Range)
      return Reg_Fault_Event_Data_Type;

   procedure Write_Fault_Event_Data
     (Index : IOMMU_Device_Range;
      Value : Reg_Fault_Event_Data_Type);

   function Read_IOTLB_Invalidate
     (Index : IOMMU_Device_Range)
      return Reg_IOTLB_Invalidate;

   procedure Write_IOTLB_Invalidate
     (Index : IOMMU_Device_Range;
      Value : Reg_IOTLB_Invalidate);

   procedure Write_IRT_Address
     (Index : IOMMU_Device_Range;
      Value : Reg_IRT_Address);

private

   --  IOTLB Invalidate Register offset, must be calculated using Extended
   --  Capability Register IRO field (TODO)

   IOTLB_Offset : constant := 16#10# * 16 + 8;

   --  Fault-recording register offset, must be calculcated using Capability
   --  Register FRO field (TODO).

   FR_Offset : constant := 16#20# * 16;

   --  NOTE: The Intel VT-d spec section 10.2 mentions that software is
   --  expected to access registers as a whole. To avoid side-effects from
   --  partial/wider reads always read the entire record field/register, modify
   --  the appropriate values and write back the new data (see also GNATtracker
   --  ticket N307-023).

   type IOMMU_Common_Type is record
      Version             : Reg_Version_Type;
      Reserved_1          : SK.Word32;
      Capability          : Reg_Capability_Type;
      Ext_Capability      : Reg_Extcapability_Type;
      Global_Command      : Reg_Global_Command_Type;
      Global_Status       : Reg_Global_Status_Type;
      Root_Table_Address  : SK.Word64;
      Context_Command     : Reg_Context_Command_Type;
      Reserved_2          : SK.Word32;
      Fault_Status        : Reg_Fault_Status_Type;
      Fault_Event_Control : Reg_Fault_Event_Control_Type;
      Fault_Event_Data    : Reg_Fault_Event_Data_Type;
      Fault_Event_Address : Reg_Fault_Event_Address_Type;
      IRT_Address         : Reg_IRT_Address;
   end record;

   pragma Warnings (Off, "*-bit gap before component *");
   for IOMMU_Common_Type use record
      Version             at 16#00# range 0 .. 31;
      Reserved_1          at 16#04# range 0 .. 31;
      Capability          at 16#08# range 0 .. 63;
      Ext_Capability      at 16#10# range 0 .. 63;
      Global_Command      at 16#18# range 0 .. 31;
      Global_Status       at 16#1c# range 0 .. 31;
      Root_Table_Address  at 16#20# range 0 .. 63;
      Context_Command     at 16#28# range 0 .. 63;
      Reserved_2          at 16#30# range 0 .. 31;
      Fault_Status        at 16#34# range 0 .. 31;
      Fault_Event_Control at 16#38# range 0 .. 31;
      Fault_Event_Data    at 16#3c# range 0 .. 31;
      Fault_Event_Address at 16#40# range 0 .. 31;
      IRT_Address         at 16#b8# range 0 .. 63;
   end record;
   pragma Warnings (On, "*-bit gap before component *");

   type IOMMU_1_Type is record
      Common           : IOMMU_Common_Type;
      IOTLB_Invalidate : Reg_IOTLB_Invalidate;
      Fault_Recording  : Reg_Fault_Recording_Type;
   end record;

   pragma Warnings (Off, "*-bit gap before component *");
   for IOMMU_1_Type use record
      IOTLB_Invalidate at IOTLB_Offset range 0 .. 63;
      Fault_Recording  at FR_Offset    range 0 .. 127;
   end record;
   pragma Warnings (On, "*-bit gap before component *");

   type IOMMU_2_Type is record
      Common           : IOMMU_Common_Type;
      IOTLB_Invalidate : Reg_IOTLB_Invalidate;
      Fault_Recording  : Reg_Fault_Recording_Type;
   end record;

   pragma Warnings (Off, "*-bit gap before component *");
   for IOMMU_2_Type use record
      IOTLB_Invalidate at IOTLB_Offset range 0 .. 63;
      Fault_Recording  at FR_Offset    range 0 .. 127;
   end record;
   pragma Warnings (On, "*-bit gap before component *");

   type Byte_Array is array (Positive range <>) of Interfaces.Unsigned_8;

   type IOMMUs_Type is record
      IOMMU_1   : IOMMU_1_Type;
      Padding_1 : Byte_Array (1 .. SK.Page_Size - IOMMU_1_Type'Size / 8);
      IOMMU_2   : IOMMU_2_Type;
      Padding_2 : Byte_Array (1 .. SK.Page_Size - IOMMU_2_Type'Size / 8);
   end record;

end IOMMU;
