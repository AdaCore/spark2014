with System;

package body IOMMU
with
   SPARK_Mode,
   Refined_State => (State => IOMMUs)
is

   IOMMUs : IOMMUs_Type
     with
       Volatile,
       Async_Writers,
       Async_Readers,
       Effective_Writes,
       Address => System'To_Address (Base_Address);

   -------------------------------------------------------------------------

   function Read_Capability
     (Index : IOMMU_Device_Range)
      return Reg_Capability_Type
   is
      Value : Reg_Capability_Type;
   begin
      case Index is
         when 1 => Value := IOMMUs.IOMMU_1.Common.Capability;
         when 2 => Value := IOMMUs.IOMMU_2.Common.Capability;
      end case;

      return Value;
   end Read_Capability;

   -------------------------------------------------------------------------

   function Read_Context_Command
     (Index : IOMMU_Device_Range)
      return Reg_Context_Command_Type
   is
      Value : Reg_Context_Command_Type;
   begin
      case Index is
         when 1 => Value := IOMMUs.IOMMU_1.Common.Context_Command;
         when 2 => Value := IOMMUs.IOMMU_2.Common.Context_Command;
      end case;

      return Value;
   end Read_Context_Command;

   -------------------------------------------------------------------------

   function Read_Extended_Capability
     (Index : IOMMU_Device_Range)
      return Reg_Extcapability_Type
   is
      Value : Reg_Extcapability_Type;
   begin
      case Index is
         when 1 => Value := IOMMUs.IOMMU_1.Common.Ext_Capability;
         when 2 => Value := IOMMUs.IOMMU_2.Common.Ext_Capability;
      end case;

      return Value;
   end Read_Extended_Capability;

   -------------------------------------------------------------------------

   function Read_Fault_Event_Address
     (Index : IOMMU_Device_Range)
      return Reg_Fault_Event_Address_Type
   is
      Value : Reg_Fault_Event_Address_Type;
   begin
      case Index is
         when 1 => Value := IOMMUs.IOMMU_1.Common.Fault_Event_Address;
         when 2 => Value := IOMMUs.IOMMU_2.Common.Fault_Event_Address;
      end case;

      return Value;
   end Read_Fault_Event_Address;

   -------------------------------------------------------------------------

   function Read_Fault_Event_Control
     (Index : IOMMU_Device_Range)
      return Reg_Fault_Event_Control_Type
   is
      Value : Reg_Fault_Event_Control_Type;
   begin
      case Index is
         when 1 => Value := IOMMUs.IOMMU_1.Common.Fault_Event_Control;
         when 2 => Value := IOMMUs.IOMMU_2.Common.Fault_Event_Control;
      end case;

      return Value;
   end Read_Fault_Event_Control;

   -------------------------------------------------------------------------

   function Read_Fault_Event_Data
     (Index : IOMMU_Device_Range)
      return Reg_Fault_Event_Data_Type
   is
      Value : Reg_Fault_Event_Data_Type;
   begin
      case Index is
         when 1 => Value := IOMMUs.IOMMU_1.Common.Fault_Event_Data;
         when 2 => Value := IOMMUs.IOMMU_2.Common.Fault_Event_Data;
      end case;

      return Value;
   end Read_Fault_Event_Data;

   -------------------------------------------------------------------------

   function Read_Fault_Recording
     (Index : IOMMU_Device_Range)
      return Reg_Fault_Recording_Type
   is
      Value : Reg_Fault_Recording_Type;
   begin
      case Index is
         when 1 => Value := IOMMUs.IOMMU_1.Fault_Recording;
         when 2 => Value := IOMMUs.IOMMU_2.Fault_Recording;
      end case;

      return Value;
   end Read_Fault_Recording;

   -------------------------------------------------------------------------

   function Read_Fault_Status
     (Index : IOMMU_Device_Range)
      return Reg_Fault_Status_Type
   is
      Value : Reg_Fault_Status_Type;
   begin
      case Index is
         when 1 => Value := IOMMUs.IOMMU_1.Common.Fault_Status;
         when 2 => Value := IOMMUs.IOMMU_2.Common.Fault_Status;
      end case;

      return Value;
   end Read_Fault_Status;

   -------------------------------------------------------------------------

   function Read_Global_Status
     (Index : IOMMU_Device_Range)
      return Reg_Global_Status_Type
   is
      Value : Reg_Global_Status_Type;
   begin
      case Index is
         when 1 => Value := IOMMUs.IOMMU_1.Common.Global_Status;
         when 2 => Value := IOMMUs.IOMMU_2.Common.Global_Status;
      end case;

      return Value;
   end Read_Global_Status;

   -------------------------------------------------------------------------

   function Read_IOTLB_Invalidate
     (Index : IOMMU_Device_Range)
      return Reg_IOTLB_Invalidate
   is
      Value : Reg_IOTLB_Invalidate;
   begin
      case Index is
         when 1 => Value := IOMMUs.IOMMU_1.IOTLB_Invalidate;
         when 2 => Value := IOMMUs.IOMMU_2.IOTLB_Invalidate;
      end case;

      return Value;
   end Read_IOTLB_Invalidate;

   -------------------------------------------------------------------------

   function Read_Version
     (Index : IOMMU_Device_Range)
      return Reg_Version_Type
   is
      Value : Reg_Version_Type;
   begin
      case Index is
         when 1 => Value := IOMMUs.IOMMU_1.Common.Version;
         when 2 => Value := IOMMUs.IOMMU_2.Common.Version;
      end case;

      return Value;
   end Read_Version;

   -------------------------------------------------------------------------

   procedure Write_Context_Command
     (Index : IOMMU_Device_Range;
      Value : Reg_Context_Command_Type)
   is
   begin
      case Index is
         when 1 => IOMMUs.IOMMU_1.Common.Context_Command := Value;
         when 2 => IOMMUs.IOMMU_2.Common.Context_Command := Value;
      end case;
   end Write_Context_Command;

   -------------------------------------------------------------------------

   procedure Write_Fault_Event_Address
     (Index : IOMMU_Device_Range;
      Value : Reg_Fault_Event_Address_Type)
   is
   begin
      case Index is
         when 1 => IOMMUs.IOMMU_1.Common.Fault_Event_Address := Value;
         when 2 => IOMMUs.IOMMU_2.Common.Fault_Event_Address := Value;
      end case;
   end Write_Fault_Event_Address;

   -------------------------------------------------------------------------

   procedure Write_Fault_Event_Control
     (Index : IOMMU_Device_Range;
      Value : Reg_Fault_Event_Control_Type)
   is
   begin
      case Index is
         when 1 => IOMMUs.IOMMU_1.Common.Fault_Event_Control := Value;
         when 2 => IOMMUs.IOMMU_2.Common.Fault_Event_Control := Value;
      end case;
   end Write_Fault_Event_Control;

   -------------------------------------------------------------------------

   procedure Write_Fault_Event_Data
     (Index : IOMMU_Device_Range;
      Value : Reg_Fault_Event_Data_Type)
   is
   begin
      case Index is
         when 1 => IOMMUs.IOMMU_1.Common.Fault_Event_Data := Value;
         when 2 => IOMMUs.IOMMU_2.Common.Fault_Event_Data := Value;
      end case;
   end Write_Fault_Event_Data;

   -------------------------------------------------------------------------

   procedure Write_Fault_Recording
     (Index : IOMMU_Device_Range;
      Value : Reg_Fault_Recording_Type)
   is
   begin
      case Index is
         when 1 => IOMMUs.IOMMU_1.Fault_Recording := Value;
         when 2 => IOMMUs.IOMMU_2.Fault_Recording := Value;
      end case;
   end Write_Fault_Recording;

   -------------------------------------------------------------------------

   procedure Write_Fault_Status
     (Index : IOMMU_Device_Range;
      Value : Reg_Fault_Status_Type)
   is
   begin
      case Index is
         when 1 => IOMMUs.IOMMU_1.Common.Fault_Status := Value;
         when 2 => IOMMUs.IOMMU_2.Common.Fault_Status := Value;
      end case;
   end Write_Fault_Status;

   -------------------------------------------------------------------------

   procedure Write_Global_Command
     (Index : IOMMU_Device_Range;
      Value : Reg_Global_Command_Type)
   is
   begin
      case Index is
         when 1 => IOMMUs.IOMMU_1.Common.Global_Command := Value;
         when 2 => IOMMUs.IOMMU_2.Common.Global_Command := Value;
      end case;
   end Write_Global_Command;

   -------------------------------------------------------------------------

   procedure Write_IOTLB_Invalidate
     (Index : IOMMU_Device_Range;
      Value : Reg_IOTLB_Invalidate)
   is
   begin
      case Index is
         when 1 => IOMMUs.IOMMU_1.IOTLB_Invalidate := Value;
         when 2 => IOMMUs.IOMMU_2.IOTLB_Invalidate := Value;
      end case;
   end Write_IOTLB_Invalidate;

   -------------------------------------------------------------------------

   procedure Write_IRT_Address
     (Index : IOMMU_Device_Range;
      Value : Reg_IRT_Address)
   is
   begin
      case Index is
         when 1 => IOMMUs.IOMMU_1.Common.IRT_Address := Value;
         when 2 => IOMMUs.IOMMU_2.Common.IRT_Address := Value;
      end case;
   end Write_IRT_Address;

   -------------------------------------------------------------------------

   procedure Write_Root_Table_Address
     (Index : IOMMU_Device_Range;
      Value : SK.Word64)
   is
   begin
      case Index is
         when 1 => IOMMUs.IOMMU_1.Common.Root_Table_Address := Value;
         when 2 => IOMMUs.IOMMU_2.Common.Root_Table_Address := Value;
      end case;
   end Write_Root_Table_Address;

end IOMMU;
