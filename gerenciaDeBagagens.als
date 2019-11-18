module gerenciaDeBagagens

---SIGS---
sig ticket{
	donoTk : one passageiro
}
	
abstract sig bagagem{
	donoBg : one passageiro
}


sig bagagemLeve extends bagagem{}
sig bagagemMediana extends bagagem{}
sig bagagemPesada extends bagagem{}


abstract sig passageiro{
	bagagemPas : set bagagem,
	ticketPas : one ticket
}

sig passageiroComun extends passageiro{}

sig passageiroMilhagem extends passageiro{}

sig passageiroVip extends passageiro{}


---FACTS---
fact passageiroF {
	some q: passageiro | some q.bagagemPas || no q.bagagemPas
}

fact bagagemF {
	all b: bagagem | one b.donoBg
	all b: bagagem, p: passageiro | b in p.bagagemPas 
}

fact ticketF {
	all t: ticket, p: passageiro | p in t.donoTk and t in p.ticketPas
}

pred show[]{}
run show for 5
