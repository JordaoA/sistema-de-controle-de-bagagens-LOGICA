module gerenciaDeBagagens

					---SIGS---
---Assintura para o ticket---
sig ticket{
	donoTk : one passageiro
}
---Assintura para o ticket---	
abstract sig bagagem{
	donoBg : one passageiro
}

sig bagagemLeve extends bagagem{} ---Assintura para o Bagagem Leve---
sig bagagemMedia extends bagagem{} ---Assintura para o Bagagem Media---
sig bagagemPesada extends bagagem{} ---Assintura para o Bagagem Pesada---

---Assintura para o passageiro abstrato---
abstract sig passageiro{
	ticketPas : one ticket
}

---Assintura para o passageiro Comum---
sig passageiroComum extends passageiro{
	bagagemLevePas : lone bagagemLeve,
	bagagemPesadaPas : lone bagagemPesada,
	bagagemMediaPas : lone bagagemMedia

}

---Assintura para o passageiro Milhagem---
sig passageiroMilhagem extends passageiro{
	bagagemLevePas : lone bagagemLeve,
	bagagemPesadaPas : lone bagagemPesada,
	bagagemMediaPas : lone bagagemMedia
}

---Assintura para o passageiro Vip---
sig passageiroVip extends passageiro{
	bagagemLevePas : set bagagemLeve,
	bagagemPesadaPas : set bagagemPesada,
	bagagemMediaPas : set bagagemMedia
}
					---FIM DAS SIGS---

					---FACTS---

---Fatos relacionados ao passageiro
fact passageiroF {

--- passageiro Comum
	all pc : passageiroComum | lone pc.bagagemLevePas && lone pc.bagagemPesadaPas 
		&& no pc.bagagemMediaPas

--- passageiro de Milhagem
	all pm : passageiroMilhagem | lone pm.bagagemLevePas && lone pm.bagagemPesadaPas 
		&& lone pm.bagagemMediaPas

--- passageiro Vip
	all pv : passageiroVip| lone pv.bagagemLevePas && #(pv.bagagemPesadaPas) <= 2 
		&& #(pv.bagagemMediaPas) <= 2

}

---Fatos relacionados a bagagem do passageiro.
fact bagagemF {
	---Bagagem generica
	all b: bagagem | one b.donoBg

	---Passageiro Comum
	all bl: bagagemLeve, pc: passageiroComum | bl in pc.bagagemLevePas
	all bp: bagagemPesada, pc: passageiroComum | bp in pc.bagagemPesadaPas
	all bm: bagagemMedia, pc: passageiroComum | bm in pc.bagagemMediaPas

	---Passageiro Milhagem
	all bl: bagagemLeve, pm: passageiroMilhagem | bl in pm.bagagemLevePas
	all bp: bagagemPesada, pm: passageiroMilhagem | bp in pm.bagagemPesadaPas
	all bm: bagagemMedia, pm: passageiroMilhagem | bm in pm.bagagemMediaPas
	
	---Passageiro VIP
	all bl: bagagemLeve, pv: passageiroVip | bl in pv.bagagemLevePas
	all bp: bagagemPesada, pv: passageiroVip | bp in pv.bagagemPesadaPas
	all bm: bagagemMedia, pv: passageiroVip | bm in pv.bagagemMediaPas
}

---Fatos relacionados ao passageiro
fact ticketF {
	all t: ticket, p: passageiro | p in t.donoTk and t in p.ticketPas
}

					---FIM DOS FATOS---

pred show[]{}
run show for 10
