package P is

type Type_0 is new Integer;

type Type_1 is record
   Field_0 : Type_0;
   Field_1 : Type_0;
   Field_2 : Type_0;
   Field_3 : Type_0;
   Field_4 : Type_0;
   Field_5 : Type_0;
   Field_6 : Type_0;
   Field_7 : Type_0;
end record;

function Create_Type_1 return Type_1
with Global => null,
     Post   => Create_Type_1'Result.Field_0 = 0 and then
               Create_Type_1'Result.Field_1 = 0 and then
               Create_Type_1'Result.Field_2 = 0 and then
               Create_Type_1'Result.Field_3 = 0 and then
               Create_Type_1'Result.Field_4 = 0 and then
               Create_Type_1'Result.Field_5 = 0 and then
               Create_Type_1'Result.Field_6 = 0 and then
               Create_Type_1'Result.Field_7 = 0;

type Type_2 is record
   Field_0 : Type_1;
   Field_1 : Type_1;
   Field_2 : Type_1;
   Field_3 : Type_1;
   Field_4 : Type_1;
end record;

function Create_Type_2 return Type_2
with Global => null,
     Post   => Create_Type_2'Result.Field_0 = Create_Type_1 and then
               Create_Type_2'Result.Field_1 = Create_Type_1 and then
               Create_Type_2'Result.Field_2 = Create_Type_1 and then
               Create_Type_2'Result.Field_3 = Create_Type_1 and then
               Create_Type_2'Result.Field_4 = Create_Type_1;

type Type_3 is new Integer;

type Type_4 is record
   Field_0 : Type_1;
   Field_1 : Type_1;
   Field_2 : Type_2;
   Field_3 : Type_2;
end record;

function Create_Type_4 return Type_4
with Global => null,
     Post   => Create_Type_4'Result.Field_0 = Create_Type_1 and then
               Create_Type_4'Result.Field_1 = Create_Type_1 and then
               Create_Type_4'Result.Field_2 = Create_Type_2 and then
               Create_Type_4'Result.Field_3 = Create_Type_2;

type Type_5 is record
   Field_0 : Type_3;
   Field_1 : Type_4;
   Field_2 : Type_2;
   Field_3 : Type_4;
   Field_4 : Type_4;
end record;

function Create_Type_5 return Type_5
with Global => null,
     Post   => Create_Type_5'Result.Field_0 = 0 and then
               Create_Type_5'Result.Field_1 = Create_Type_4 and then
               Create_Type_5'Result.Field_2 = Create_Type_2 and then
               Create_Type_5'Result.Field_3 = Create_Type_4 and then
               Create_Type_5'Result.Field_4 = Create_Type_4;

type Type_6 is record
   Field_0 : Type_1;
   Field_1 : Type_5;
   Field_2 : Type_2;
   Field_3 : Type_5;
end record;

function Create_Type_6 return Type_6
with Global => null,
     Post   => Create_Type_6'Result.Field_0 = Create_Type_1 and then
               Create_Type_6'Result.Field_1 = Create_Type_5 and then
               Create_Type_6'Result.Field_2 = Create_Type_2 and then
               Create_Type_6'Result.Field_3 = Create_Type_5;

type Type_7 is new Integer;

type Type_8 is record
   Field_0 : Type_4;
   Field_1 : Type_5;
   Field_2 : Type_4;
   Field_3 : Type_6;
   Field_4 : Type_5;
   Field_5 : Type_7;
   Field_6 : Type_1;
   Field_7 : Type_5;
end record;

function Create_Type_8 return Type_8
with Global => null,
     Post   => Create_Type_8'Result.Field_0 = Create_Type_4 and then
               Create_Type_8'Result.Field_1 = Create_Type_5 and then
               Create_Type_8'Result.Field_2 = Create_Type_4 and then
               Create_Type_8'Result.Field_3 = Create_Type_6 and then
               Create_Type_8'Result.Field_4 = Create_Type_5 and then
               Create_Type_8'Result.Field_5 = 0 and then
               Create_Type_8'Result.Field_6 = Create_Type_1 and then
               Create_Type_8'Result.Field_7 = Create_Type_5;

end P;
