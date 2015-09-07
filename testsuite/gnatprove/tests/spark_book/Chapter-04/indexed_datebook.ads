with Dates;
package Indexed_Datebook
  with
    SPARK_Mode     => On,
    Abstract_State => State
is
   type Status_Type is (Success, Description_Too_Long, Insufficient_Space);

   procedure Initialize
     with
       Global  => (Output => State),
       Depends => (State => null);

   procedure Compact_Index
     with
       Global  => (In_Out => State),
       Depends => (State =>+ null);

   procedure Add_Event (Description : in  String;
                        Date        : in  Dates.Datetime;
                        Status      : out Status_Type)
     with
       Global  => (In_Out => State),
       Depends => (State  =>+ (Description, Date),
                   Status =>  (Description, State) );

end Indexed_Datebook;
