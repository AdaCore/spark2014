package body P is

function Create_Type_1 return Type_1
is
begin
   return (Field_0 => 0,
           Field_1 => 0,
           Field_2 => 0,
           Field_3 => 0,
           Field_4 => 0,
           Field_5 => 0,
           Field_6 => 0,
           Field_7 => 0);
end Create_Type_1;

function Create_Type_2 return Type_2
is
begin
   return (Field_0 => Create_Type_1,
           Field_1 => Create_Type_1,
           Field_2 => Create_Type_1,
           Field_3 => Create_Type_1,
           Field_4 => Create_Type_1);
end Create_Type_2;

function Create_Type_4 return Type_4
is
begin
   return (Field_0 => Create_Type_1,
           Field_1 => Create_Type_1,
           Field_2 => Create_Type_2,
           Field_3 => Create_Type_2);
end Create_Type_4;

function Create_Type_5 return Type_5
is
begin
   return (Field_0 => 0,
           Field_1 => Create_Type_4,
           Field_2 => Create_Type_2,
           Field_3 => Create_Type_4,
           Field_4 => Create_Type_4);
end Create_Type_5;

function Create_Type_6 return Type_6
is
begin
   return (Field_0 => Create_Type_1,
           Field_1 => Create_Type_5,
           Field_2 => Create_Type_2,
           Field_3 => Create_Type_5);
end Create_Type_6;

function Create_Type_8 return Type_8
is
begin
   return (Field_0 => Create_Type_4,
           Field_1 => Create_Type_5,
           Field_2 => Create_Type_4,
           Field_3 => Create_Type_6,
           Field_4 => Create_Type_5,
           Field_5 => 0,
           Field_6 => Create_Type_1,
           Field_7 => Create_Type_5);
end Create_Type_8;

end P;
