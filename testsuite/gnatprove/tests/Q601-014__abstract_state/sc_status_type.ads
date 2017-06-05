--++ package Safety_Monitor
--------------------------------------------------------------------------------
-- UNIT NAME       : Sc_Status_Type
-- UNIT KIND       : Package Specification
-- FILENAME        : sc_status_type.ads
-- SYSTEM          : AW159_Wildcat_SMS_Safety_Monitor_Design_Model
--
-- MODEL DOCUMENTATION
-- Abstract Data Type for state items representing a single status
--
--------------------------------------------------------------------------------


package Sc_Status_Type with SPARK_Mode  is

 
    type Duplicate_Status_Type is
	record
	    Prime, Shadow : Boolean;
	end record;

    -- This type is represented such that the Prime and Shadow elements
    -- are always on different 16 bit devices
    for Duplicate_Status_Type use
	record
	    Prime at 0 range 0 .. 0;
	    Shadow at 2 range 0 .. 0;
	end record;

   
    type Object_Type is private;
    
    --  Old SPARK Proof functionm
    --$ function Update_Object(Data:  Service_Types.Sms_State_Type)
    --$     return Object_Type;


    -- Documentation:
    --    This operation returns the value of an instance of
    --    the type.
    --
    function Read (This : in Object_Type) return Boolean;

    -- Documentation:
    --    This operation updates an instance of the type to the
    --    supplied value.
    --
    procedure Write (This : out Object_Type; Data : in Boolean);
    --$ derives
    --$ This from Data;
    --$ post
    --$         This = Update_Object (Data)
    --$ ;

    -- Documentation:
    --    This operation returns the required initial value of
    --    an instance of this type.
    --
    function Initialise return Object_Type;


private


    type Object_Type is
	record

	    -- Data Members for Class Attributes
	    -- Documentation:
	    --    This attribute represents an instance of the
	    --    duplicated type.
	    Sc_State : Duplicate_Status_Type;

	end record;


end Sc_Status_Type;
