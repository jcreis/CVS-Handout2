class Row {

    var name: array<char>;
    var age: int;
    constructor()
    {   
        this.name := new char[0];
        this.age := 0;
    }

    method setName(nome: array<char>)
    modifies this

    requires nome.Length > 0

    ensures this.name.Length > 0
    {
        this.name := nome;
    }

    method setAge(idade: int) 
    modifies this

    requires idade >= 0;

    ensures this.age >= 0;
    {
        this.age := idade;
    }
   
}






class PersonDB {
    var db:array<Row>;
    var size:int;

    constructor() 
        ensures fresh(db)
    {
        this.db := new Row?[10];
        this.size := 0;
    }

    method add() returns (index:int)
        modifies this.db, this`size

        requires this.db.Length > size
    {
        if( 0 <= size < db.Length ) {
            db[size] := new Row();
            size := size + 1;
        }
    }

    method delete(i:int) 
        modifies this.db //, this`size
        
    {
        if( 0 <= i < db.Length ) {
            db[i] := new Row();
            //size := size - 1;
        }
    }

   /*  method save(name: string, age: int) returns (id:int)
    {

    } */

    /* method update(name: string, age: int, id: int)
    {

    } */

    method find(id: int) returns (p: Person?)
    requires 0 <= id < db.Length
    requires 0 <= id < size
    {
        p := null;
        if(db[id] != null){
            if(db[id].name.Length > 0 && db[id].age >= 0){
               p := new Person();
               p.setAge(db[id].age);
               p.setName(db[id].name);
               p.setConnection(this);
           }
       }
       return p;
    }

}



class Person {
    var name: array<char>;
    var age: int;
    var id: int;
    var connection: PersonDB?;
    
    constructor() 
    ensures Transient()
    {
        this.name := new char[0];
        this.age := 0;
        this.connection := null;
        this.id := -1;
    }


    method save(p: PersonDB?)
    modifies this`id, this`connection

    requires Transient()
    requires p != null
    requires p.db.Length > 0
    requires this.id == -1
    requires this.name.Length > 0 && this.age >= 0
    requires p.db.Length > p.size

    ensures Persitent()
    ensures p != null ==> this.connection != null
    ensures this.name.Length > 0
    ensures this.age >= 0
    {
        this.setConnection(p);
        var pplDB := this.connection.db;
        var pos := this.id;
        if(this.id < 0){
            pos := connection.add();
        }
       

        pplDB[pos].setName(this.name);
        pplDB[pos].setAge(this.age);

        this.setID(pos);
    }




    method close()
    modifies this`connection

    requires Persitent()
    requires this.id > -1
    requires this.connection != null
    requires this.name.Length > 0 && this.age >= 0

    ensures Detached()
    ensures this.connection == null
    ensures this.id > -1
    {
        this.setConnection(null);
    }




    method update(p: PersonDB)
    modifies this`connection

    requires Detached()
    requires p != null
    requires this.id > -1
    requires this.connection == null
    requires this.name.Length > 0 && this.age >= 0

    ensures Persitent()
    ensures this.id > -1
    ensures this.connection != null
    {
        this.setConnection(p);
    }





    method delete()
    modifies this`id

    requires Persitent()
    requires this.id > -1
    requires connection != null
    requires this.name.Length > 0 && this.age >= 0

    ensures Transient()
    ensures this.id == -1
    {
        this.setID(-1);
    }






    method setName(nome: array<char>)
    modifies this`name
    {
        this.name:= nome;
    }

    method setAge(idade: int)
    modifies this`age
    {
        this.age:= idade;
    }

    method setID(id: int)
    modifies this`id
    {
        this.id:= id;
    }

    method setConnection(connect: PersonDB?)
    modifies this`connection
    {
        this.connection:= connect;
    }



    function Transient():bool
 	reads this
 	{ 
         if(id == -1) then true
         else false
    }
 	
 	function Persitent():bool
 	reads this
 	{   
         if(id > -1 && connection != null) then true
         else false
    } 

 	function Detached():bool
 	reads this
    
 	{ 
         if(id > -1 && connection == null) then true
         else false
    } 



}

    
