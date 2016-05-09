#!/usr/bin/python2
#this could use some cleanup, like breaking the classes into their own files...
import pygame, numpy as np, sys, random, math, time, glob, os
from collections import defaultdict
import eztext
try:
	import win32clipboard
except ImportError:
	print "Clipboard not working"

base64 = []#base64?
base64.extend(chr(i) for i in xrange(ord("a"), ord("z")+1))
base64.extend(chr(i) for i in xrange(ord("A"), ord("Z")+1))
base64.extend(chr(i) for i in xrange(ord("0"), ord("9")+1))
base64.extend(["+", "-"])
base64 = tuple(base64)#store as string instead? interfaces the same anyway...


#hepers:
def clamp(val, min, max):
	if val < min:
		return min
	elif val > max:
		return max
	return val
def sign(val):
	if val > 0:
		return 1
	elif val < 0:
		return -1
	return 0
def rollD4():
	return random.randrange(1, 5)
def rollD6():
	return random.randrange(1, 7)
def rollD20():
	return random.randrange(1, 21)
def rollAttack(base):#returns dmg
	r = rollD20()
	if r == 20:
		return (base+r)*2
	elif r == 1:
		return 0
	return base + r
def rollDefense(dmg, DEF):#returns actual dmg
	r = rollD20()
	if r == 20:
		return dmg - (DEF+r)*2
	elif r == 1:
		return dmg*2
	return dmg - DEF - r

#parser/compiler:
class ScripterBaseError(Exception): pass#base
class TokenizerSyntaxError(ScripterBaseError): pass#errors during tokenizing
class ParserSyntaxError(ScripterBaseError): pass#errors during parsong
class ExecutionError(ScripterBaseError): pass#errors during execution, illegal actions mainly. these should be handled by Script()
class ExecutionTurnEnd(ExecutionError): pass

class Script():
	#SYNTAX = defaultdict(lambda: [])#["ADD"] = list, i = (operands like "RR", python function)
	SYNTAX = {}#["ADD"] = (python function, syntax1, syntax2, ... , syntaxX)
	#syntax: "RR"
	#"operands":
	#	"C" - constant
	#	"R" - register value
	#	"P" - register index/pointer (requires writeable)
	#	"S" - string/word (eg. ability name)
	def __init__(self):#todo: implement self.illegalGotos
		#program data
		self.bytecode = None
		self.instructions = []
		self.subrutines = {}#id:instruction pos to SUR call declaring the subrutine
		
		#actor and enviroment, set when executing:
		self.berserker = None
		self.map = None
		
		#memory:
		self.registers = []#i = value of same register in same position as in regnames
		self.regnames = []#i = (string name, bool writeable)
		
		#Execution variables:
		self.illegalGotos = []#extended with ranges of subrutine areas in self.instructions
		self.Calls = []#used to keep track of where SUE should return
		self.PROG = self.MakeRegisterPropertyObject("PROG", readonly=True)#denotes where in self.instructions we are. .value makes it impollsible to write diretly to the property
		self.TargetIndex = 0
		
		#debug:
		self.registerChanges = (None, None)#("registername", callback(value))
		self.actionLimit = 10000
		
		self.clean()
	def clean(self):
		self.registers = []
		self.regnames = []
		self.instructions = []
		self.subrutines = {}
		self.illegalGotos = []
		#self.PROG.value = 0
		
		#Set hardcoded registers and symbols:
		for name in ("PROG", "RES", "HP", "MP", "SP", "ATT", "MAG", "MOV", "ACT", "RANGE"):
			self.regnames.append((name, name=="RES"))
			self.registers.append(0)
		self.baseSymbols = {"L":0, "R":1}#hardcoded constants
	def load(self, data, source=False, bytecode=False):#todo: handle fetcing registers
		assert source ^ bytecode# xor
		self.clean()
		
		if source:
			tokens, symbols, registernames = self.tokenize(data)
			
			for name in registernames:
				if name not in map(lambda x: x[0], self.regnames):
					self.regnames.append((name, True))
					self.registers.append(0)
			
			self.instructions, self.subrutines = self.parse(tokens, symbols)
			
			self.bytecode = self.compile(self.instructions)
		else:
			self.bytecode = data
			self.instructions, self.subrutines, registernames = self.decompile(data)
			for name in registernames:
				self.regnames.append((name, True))
				self.registers.append(0)
	def loadSource(self, data): self.load(data, source=True)
	def loadBytecode(self, data): self.load(data, bytecode=True)
	#compiler
	def getBytecode(self):
		assert self.bytecode
		return self.bytecode
	def tokenize(self, data):#todo: adding of RO registers
		symbols = self.baseSymbols.copy()
		tokens = []
		lines = data.replace("\r\n", "\n").replace("\r", "\n").replace("\n\t", "\n").split("\n")[::-1]
		lineNum = 0
		
		while lines:
			lineraw = lines.pop()
			line = lineraw.split("#")[0].replace("\t", " ").split(" ")[::-1]
			lineNum += 1
			
			if line[-1].upper() not in self.SYNTAX:#.keys():
				#print line[-1].upper()
				if lineraw.split("#")[0]:
					raise TokenizerSyntaxError, "Line %i: \"%s\"" % (lineNum, lineraw)
				#	print "line ignored: \"%s\"" % lineraw
				continue
			
			token = [line.pop()]
			while line:
				symboled = False
				curr = line.pop()
				if curr:
					if curr[0] in "({[":
						if symboled:
							raise TokenizerSyntaxError, "Line %i: Symbol not at the end: \"%s\"" % (lineNum, lineraw)
						
						if curr[-1] <> {"(":")", "[":"]", "{":"}"}[curr[0]]:
							raise TokenizerSyntaxError, "Line %i: Unclosed operand: " + (lineNum, curr)
						token.append(curr)
					else:
						if curr.replace("_", "").replace("-", "").isalnum():
							symboled = True
							symbols[curr] = len(tokens)
						else:
							raise TokenizerSyntaxError, "Line %i: Non-alphanumeric symbol: \"%s\"" % (lineNum, curr)
			
			tokens.append(token)
		
		#fetch variable names:
		registernames = set()
		for i in tokens:
			for operand in i[:]:
				if operand[0] == "{" and operand[-1] == "}":
					if operand[1:-1] not in registernames:
						registernames.add(operand[1:-1])
		
		return tokens, symbols, registernames
	def parse(self, tokens, symbols):#requires registers to be loaded
		instructions = []#i = ("CMD", *args), arg = (bool registerIndex, value)
		subrutines = {}#id:instruction pos to SUR call declaring the subrutine
		
		for token in tokens:
			instruction = [token[0]]
			syntax = self.SYNTAX[token[0]][1:]
			
			#parse operand types, converts symbols to value, converts registernames to indexes
			for i, operand in enumerate(token[1:]):
				value = operand[1:-1]#strip brackets
				
				if operand[0] == "(":#constant or symbol
					assert operand[-1] == ")"
					
					try:
						value = int(value)
					except ValueError:
						#print value, symbols
						if value in symbols:
							value = symbols[value]
						else:
							for ops in syntax:
								if ops[i] == "S":#the argument could be a string
									break
							else:
								raise ParserSyntaxError, "Invalid constant %s" % operand
					
					instruction.append((False, value))
				elif operand[0] == "{":#variable name
					assert operand[-1] == "}"
					
					if value not in map(lambda x: x[0], self.regnames):
						raise ParserSyntaxError, "Undeclared register name %s" % operand
					
					value = map(lambda x: x[0], self.regnames).index(value)
					
					instruction.append((True, value))
				elif operand[0] == "[":#return value N/A
					assert operand[-1] == "]"
					raise ParserSyntaxError, "[] is illegal"
				else:#lolwut
					raise ParserSyntaxError, "Something went wrong: %s" % token
			
			#syntax legality check:
			for ops in syntax:
				#print instruction, ops
				if len(instruction)-1 <> len(ops):
					continue
				
				#go over every operand and syntax description
				for op, inst in zip(ops, instruction[1:]):
					if inst[0]:#value is a register index
						if op not in "RP":
							break
						if op == "P" and not self.regnames[inst[1]][1]:
							#writeable required, but not present
							break
				else:#all match
					break
			else:
				raise ParserSyntaxError, "The operands do not match %s's syntax: \"%s\"" % (token[0], " ".join(token))
			
			instructions.append(instruction)
			if instruction[0] == "SUR":
				id = instruction[1][1]
				subrutines[id] = len(instructions)-1
		
		return instructions, subrutines
	def compile(self, instructions):#pack to "bytecode"
		self.instructions
		self.subrutines#?
		self.regnames#store names, are needed for errorhandling
		pass
	def decompile(self, bytecode):#parse from "bytecode"
		pass
	#executor
	def promptUser(self, prompt):#to be overwritten
		ret = raw_input("%s [Y/n]: " % prompt)
		return not ret or ret[0].lower() == "y"
	def errorCallback(self, text):#to be overwritten
		print text
	def runTurn(self, berserker, map):#returns true if the end is reached
		self.berserker = berserker
		self.map = map
		
		mov = self.ReadRegister("MOV")
		act = self.ReadRegister("ACT")
		self.TargetIndex = 0
		calls = 0
		
		while 1:
			try:
				self.runInstruction()
				calls += 1
				if calls > self.actionLimit: raise ExecutionError, "Hit %i action limit" % self.actionLimit
			except ExecutionError as e:
				if type(e) is ExecutionTurnEnd:#ETR / End turn
					self.PROG.value += 1
					break
				
				self.errorCallback("ExecutionError: %s" % e)
				
				#if in subroutine, exit subroutine
				if self.Calls:
					self.PROG.value = self.Calls.pop()+1
					continue
				
				#go to next ETR:
				pos = self.PROG.value
				
				while pos <= len(self.instructions):
					if self.instructions[pos][0] == "ETR":
						pos += 1
						break
					pos += 1
				
				self.PROG.value = pos
				break
		
		assert len(self.Calls) == 0
		
		self.SetRegister("MOV", mov, force=True)
		self.SetRegister("ACT", act, force=True)
		
		return self.PROG.value >= len(self.instructions)
	def runInstruction(self):#uses self.PROG.value
		if self.PROG.value >= len(self.instructions):
			raise ExecutionTurnEnd
			
		instruction = self.instructions[self.PROG.value]
		
		function = self.SYNTAX[instruction[0]][0]
		args = []
		for i, (registerindex, value) in enumerate(instruction[1:]):
			if registerindex:
				for syntax in self.SYNTAX[instruction[0]][1:]:
					if syntax[i] == "P":
						args.append(value)
						break
				else:
					args.append(self.ReadRegister(value))
			else:
				args.append(value)
		
		#print "running #%.2i" % self.PROG.value, instruction[0], " ".join(map(str, args))
		res = function(self, *args)
		if res <> None:
			self.SetRegister("RES", res, force=True)
		
		self.PROG.value += 1
	def ReadRegister(self, ID, raw=False):
		if type(ID) is str:
			ID = map(lambda x: x[0], self.regnames).index(ID)
		ret = self.registers[ID]
		
		#print "get",ID,"which is",ret
		if not raw and ret == None: return 0
		return ret
	def SetRegister(self, ID, value, force=False):
		if type(ID) is str:
			ID = map(lambda x: x[0], self.regnames).index(ID)
		
		if not force and not self.regnames[ID][1]:
			raise ExecutionError, "Read-only Register \"%s\" was written to" % self.regnames[ID][0]
		
		if self.registerChanges[0]:
			if self.regnames[ID][0] == self.registerChanges[0]:
				self.registerChanges[1](value)
		
		#print "set",ID,"to",value
		self.registers[ID] = clamp(value, -199999, 199999)
	#helpers:
	def MakeRegisterPropertyObject(self, ID, readonly=False):#it's some great fucking magic m8
		if type(ID) is str:
			if ID not in map(lambda x: x[0], self.regnames):
				self.regnames.append((ID, not readonly))
				self.registers.append(0)
				ID = len(self.regnames)-1
			else:
				ID = map(lambda x: x[0], self.regnames).index(ID)
		
		class ret(object):
			def __init__(self, executor, id):
				self.executor = executor
				self.ID = id
				self.NAME = executor.regnames[id][0]
				#self.value = 
			def get(self):
				#return self.executor.ReadRegister(self.ID, raw=True)
				return self.executor.ReadRegister(self.NAME, raw=True)
			def set(self, value):
				#self.executor.SetRegister(self.ID, value, force=True)
				self.executor.SetRegister(self.NAME, value, force=True)
			value = property(get, set)
		
		return ret(self, ID)
	def PrintRegisterChanges(self, registername, callback):
		self.registerChanges = (registername, callback)
	#commands:
	if 1:
		def cmd_StartSubrutine(self, id):
			pos = self.PROG.value + 1
			while pos < len(self.instructions):
				if self.instructions[pos][0] == "SUE":
					self.PROG.value = pos#+1
					return
				pos += 1
			
			raise ExecutionError, "instruction #%i: No matching SUE for SUR" % self.PROG.value
		SYNTAX["SUR"] = (cmd_StartSubrutine, "C")
		def cmd_EndSubrutine(self):
			self.PROG.value = self.Calls.pop()#+1
		SYNTAX["SUE"] = (cmd_EndSubrutine, "")
		def cmd_Call(self, id):
			self.Calls.append(self.PROG.value+0)
			self.PROG.value = self.subrutines[id]
		SYNTAX["CAL"] = (cmd_Call, "c")
		def cmd_Move(self, distance):
			mov = self.ReadRegister("MOV")
			if mov >= 1:
				self.SetRegister("MOV", mov-1, force=True)
				self.berserker.moveForward()
			else:
				raise ExecutionError, "instruction #%i: MOV encountered when out of MOV stat for turn" % self.PROG.value
		SYNTAX["MOV"] = (cmd_Move, "C", "R")
		def cmd_Turn(self, right):
			if right:
				self.berserker.turnRight()
			else:
				self.berserker.turnLeft()
		SYNTAX["TUR"] = (cmd_Turn, "C", "R")
		def cmd_Attack(self):
			act = self.ReadRegister("ACT")
			if act == 0:
				raise ExecutionError, "instruction #%i: ATA encountered when out of ACT stat for turn" % self.PROG.value
			self.SetRegister("ACT", act-1, force=True)
			
			self.berserker.attack()
		SYNTAX["ATA"] = (cmd_Attack, "")
		def cmd_AttackTargeted(self):
			act = self.ReadRegister("ACT")
			if act == 0:
				raise ExecutionError, "instruction #%i: ATG encountered when out of ACT stat for turn" % self.PROG.value
			self.SetRegister("ACT", act-1, force=True)
			
			self.berserker.attack(target=self.TargetIndex)
		SYNTAX["ATG"] = (cmd_AttackTargeted, "")
		def cmd_Add(self, a, b):
			return a + b
		SYNTAX["ADD"] = (cmd_Add, "RR", "RC")#, "CR")
		def cmd_Subtract(self, a, b):
			return a - b
		SYNTAX["SUB"] = (cmd_Subtract, "RR", "RC", "CR")
		#def cmd_Copy(self, source, destination):
		def cmd_SetRegister(self, value, destination):
			try:
				self.SetRegister(destination, value)
			except ExecutionError:
				cmd = self.instructions[self.PROG.value][0]
				raise ExecutionError, "instruction #%i: %s tried writing to read-only register {%s}" % (self.PROG.value, cmd, self.regnames[destination][0])
		SYNTAX["SET"] = (cmd_SetRegister, "CP")
		SYNTAX["CPY"] = (cmd_SetRegister, "RP")# SYNTAX["CPY"] = (cmd_Copy, "RP")
		def cmd_ForwardOccupied(self):
			x, y = self.berserker.dir2coord[self.berserker.dir]
			x += self.berserker.x
			y += self.berserker.y
			return 1* (self.map.isSolid(x, y) or self.map.isEntity(x, y))
		SYNTAX["OCC"] = (cmd_ForwardOccupied, "")
		def cmd_ForwardInanimate(self):
			x, y = self.berserker.dir2coord[self.berserker.dir]
			x += self.berserker.x
			y += self.berserker.y
			return 1 - 1*self.map.isEntity(x, y)
		SYNTAX["ANI"] = (cmd_ForwardInanimate, "")
		def cmd_ForwardFriendFoe(self):
			x, y = self.berserker.dir2coord[self.berserker.dir]
			x += self.berserker.x
			y += self.berserker.y
			return 1 * self.map.isFriendly(x, y)
		SYNTAX["FOF"] = (cmd_ForwardFriendFoe, "")
		def cmd_TargetCount(self):
			return len(self.berserker.listTargets())
		SYNTAX["TCN"] = (cmd_TargetCount, "")
		def cmd_Target(self, targetIndex):
			if targetIndex == 0 or targetIndex < len(self.berserker.listTargets()):
				self.TargetIndex = targetIndex
			else:
				raise ExecutionError, "instruction #%i: TGT target index higher than max. Index = (%i), #targets = %i" % (self.PROG.value, targetIndex, len(self.berserker.listTargets()))
		SYNTAX["TGT"] = (cmd_Target, "C", "R")
		def cmd_TargetInanimate(self):
			if self.TargetIndex <> 0 and self.TargetIndex >= len(self.berserker.listTargets()):
				raise ExecutionError, "instruction #%i: TAN target index higher than max. Index = (%i), #targets = %i" % (self.PROG.value, self.TargetIndex, len(self.berserker.listTargets()))
			tx, ty = self.berserker.listTargets()[self.TargetIndex]
			return 1 - 1 * self.map.isEntity(tx, ty)
		SYNTAX["TAN"] = (cmd_TargetInanimate, "")
		def cmd_TargetFriendFoe(self):
			if self.TargetIndex <> 0 and self.TargetIndex >= len(self.berserker.listTargets()):
				raise ExecutionError, "instruction #%i: TFF target index higher than max. Index = (%i), #targets = %i" % (self.PROG.value, self.TargetIndex, len(self.berserker.listTargets()))
			tx, ty = self.berserker.listTargets()[self.TargetIndex]
			return 1 * self.map.isFriendly(tx, ty)
		SYNTAX["TFF"] = (cmd_TargetFriendFoe, "")
		def cmd_Ability(self, nameStr):#todo: implement
			act = self.ReadRegister("ACT")
			if act == 0:
				raise ExecutionError, "instruction #%i: ABI encountered when out of ACT stat for turn" % self.PROG.value
			self.SetRegister("ACT", act-1, force=True)
			
			pass
		SYNTAX["ABI"] = (cmd_Ability, "S")
		def cmd_EndTurn(self):
			raise ExecutionTurnEnd
		SYNTAX["ETR"] = (cmd_EndTurn, "")
		def cmd_BranchIfFalse(self, position):
			self.cmd_Jump(position, checksOnly=True)
			if not self.ReadRegister("RES"):
				self.PROG.value = position - 1
		SYNTAX["BRZ"] = (cmd_BranchIfFalse, "C")
		def cmd_Not(self, value, destination="RES"):
			self.SetRegister(destination, 1 * (value == 0))
		#SYNTAX["NOT"] = (cmd_Not, "RP")
		SYNTAX["NOT"] = (cmd_Not, "RP", "R")#not in the spec currently...
		def cmd_And(self, a, b):
			return 1 * bool(a and b)
		SYNTAX["AND"] = (cmd_And, "RR")
		def cmd_Or(self, a, b):
			return 1 * bool(a or b)
		SYNTAX["ORR"] = (cmd_Or, "RR")
		def cmd_Jump(self, position, checksOnly=False):
			#legality check:
			cmd = self.instructions[self.PROG.value][0]#debug info
			if position >= len(self.instructions) or position < 0:
				raise ExecutionError, "instruction #%i: %s position out of bounds. pos = (%i), instruction count = %i" % (self.PROG.value, cmd, position, len(self.instructions))
			if self.Calls:
				if position < self.PROG.value:
					if position <= self.Calls[-1]:
						raise ExecutionError, "instruction #%i: %s position outside of subroutine. pos = (%i)" % (self.PROG.value, cmd, position)
					else:
						sub = 0
						for i in map(lambda x: x[0], self.instructions[self.PROG.value:position]):#no +1 intentionally
							if i == "SUR":
								sub += 1
							elif i == "SUE":
								if sub:
									sub -= 1
								else:
									raise ExecutionError, "instruction #%i: %s position outside of subroutine. pos = (%i)" % (self.PROG.value, cmd, position)
			
			#do:
			if not checksOnly:
				self.PROG.value = position - 1
		SYNTAX["JUP"] = (cmd_Jump, "C")
		def cmd_JumpRelative(self, steps):
			position = steps + self.PROG.value
			self.cmd_Jump(position)
		SYNTAX["JPR"] = (cmd_JumpRelative, "C", "R")
		def cmd_Negative(self, value):
			return 1 * bool(value < 0)
		SYNTAX["NEG"] = (cmd_Negative, "R")


#simulator:
def getClipboard():#linux, maybe someday?
	win32clipboard.OpenClipboard()
	data = win32clipboard.GetClipboardData()
	win32clipboard.CloseClipboard()
	return data

class Map():
	#enum self.data:
	t_ground = 0
	t_wall = 1
	t_friendly = 2
	t_enemy = 3
	t_hazard = 4#has no use yet, maybe used as interrupts?
	
	#checks:
	c_Solid      = (0, 1, 1, 1, 0)
	c_Friendly   = (0, 0, 1, 0, 0)
	c_Unfriendly = (0, 0, 0, 1, 0)
	c_Entity     = (0, 0, 1, 1, 0)
	def __init__(self, width, height):
		self.width = width
		self.height = height
		self.data = np.zeros((width, height), dtype=np.uint8)
		self.damages = {}#[(x, y)] = [int damage, None(ignored by Map, but is reset to None on changes to damage, used by Interface)]
	def get(self, x, y):
		if x >= 0 and y >= 0 and x < self.width and y < self.height:
			return self.data[x, y]
		else:
			return self.t_wall
	def getNeighbors(self, x, y):
		if x>0 and y > 0 and x < self.width-1 and y < self.height-1:
			return self.data[x-1:x+2, y-1:y+2]
		else:
			ret = np.ones((3, 3), dtype=np.uint8)
			
			for rx in xrange(3):
				mx = x-1+rx
				for ry in xrange(3):
					my = y-1+ry
					if mx>=0 and my>=0 and mx < self.width and my < self.height:
						ret[rx, ry] = self.data[mx, my]
			
			return ret
	def set(self, x, y, val):
		self.data[x, y] = val
	def addDamage(self, x, y, dmg):
		key = (x, y)
		val = dmg
		if key in self.damages:
			val += self.damages[key][0]
		self.damages[key] = [val, None]
	def getMoveDistance(self, (x1, y1), (x2, y2)):#enviroment ignored
		sx = sign(x2-x1)
		sy = sign(y2-y1)
		
		mov = 0
		x, y = x1, y1
		
		if sx and sy:
			while x <> x2 and y <> y2:
				x += sx
				y += sy
				mov += 1 + 1*(mov%3==0)
		
		if x <> x2:
			mov += abs(x2-x)
		
		if y <> y2:#elif, really
			mov += abs(y2-y)
		
		return mov
	def generatePossibleTargetCoords(self, x, y, dir, mov):#dir % 4 = 0->right, 1->down, 2->left and 3->up
		center = (x, y)
		distanced = {i:[] for i in xrange(1,mov+1)}
		distanced = [[] for _ in xrange(mov)]
		
		for cx in xrange(x-mov, x+mov+1):
			if 0 <= cx < self.width:
				for cy in xrange(y-mov, y+mov+1):
					if 0 <= cy < self.height:
						check = (cx, cy)
						if check <> center:
							d = self.getMoveDistance(center, check)
							if d <= mov:
								distanced[d-1].append(check)
		
		dir %= 4
		def rotation((x, y)):
			return (math.atan2(y-center[1], x-center[0])/math.pi*2 % 4 - dir) % 4
			
		for i in xrange(mov):
			for ret in sorted(distanced[i], key=rotation):
				yield ret
	#ech
	def isSolid(self, x, y):      return self.c_Solid     [self.get(x, y)] == 1
	def isFriendly(self, x, y):   return self.c_Friendly  [self.get(x, y)] == 1
	def isUnfriendly(self, x, y): return self.c_Unfriendly[self.get(x, y)] == 1
	def isEntity(self, x, y):     return self.c_Entity    [self.get(x, y)] == 1

class Berserker():
	dir2coord = (( 1,  0),
	             ( 1,  1),
	             ( 0,  1),
	             (-1,  1),
	             (-1,  0),
	             (-1, -1),
	             ( 0, -1),
	             ( 1, -1))
	allowDiagonal = False
	def __init__(self, (x, y), map):
		self.executor = Script()
		self.x = x
		self.y = y
		self.map = map
		self.dir = 0#0 = right, 2 = down, etc...
		
		self.prevPath = []#series of coordinates for where the berserker has walked, cleard between each turn
		
		#stats
		
		#these must be referenced like: self.HP.value
		self.HP = self.executor.MakeRegisterPropertyObject("HP")
		#self.MP = self.executor.MakeRegisterPropertyObject("MP")
		#self.SP = self.executor.MakeRegisterPropertyObject("SP")
		self.ATT = self.executor.MakeRegisterPropertyObject("ATT")
		#self.MAG = self.executor.MakeRegisterPropertyObject("MAG")
		self.MOV = self.executor.MakeRegisterPropertyObject("MOV")
		self.ACT = self.executor.MakeRegisterPropertyObject("ACT")
		self.RANGE = self.executor.MakeRegisterPropertyObject("RANGE")
	def load(self, data):#handles both source code and bytecode
		for i in " \t\n\r{}()[]":
			if i in data:
				self.executor.loadSource(data)
				break
		else:
			self.executor.loadBytecode(data)
	def doTurn(self):
		self.executor.runTurn(self, self.map)
	#single actions:
	def move(self, x=0, y=0):
		if not (x or y): return
		
		self.prevPath.append((self.x, self.y))
		
		#cap at +-1
		if x: x /= abs(x)
		if y: y /= abs(y)
		
		if not self.map.isSolid(self.x + x, self.y + y):
			self.x += x
			self.y += y
	def turn(self, dir):
		self.dir = dir % 8
	def attack(self, target=None):#target = index in self.listTargets(), returns true if valid target
		if target == None:#attack forward
			tx, ty = self.dir2coord[self.dir]
			tx += self.x
			ty += self.y
		else:
			targets = self.listTargets()
			if target >= len(targets):
				return False
			tx, ty = targets[target]
		
		if self.map.isEntity(tx, ty) or self.map.isSolid(tx, ty):
			self.map.addDamage(tx, ty, rollAttack(self.ATT.value))
		
		return True
	def listTargets(self, all=False, doInanimate=True):
		ret = []
		for pos in self.map.generatePossibleTargetCoords(self.x, self.y, self.dir//2, self.RANGE.value):
			if all or self.map.isEntity(pos[0], pos[1]) or (doInanimate and self.map.isSolid(pos[0], pos[1])):
				ret.append(pos)
		return ret
	#simplified action handles:
	def moveForward(self):  a, b = self.dir2coord[self.dir]; self.move(x=a, y=b)
	def moveBackward(self): a, b = self.dir2coord[self.dir]; self.move(x=-a, y=-b)
	def moveUp(self):  	 self.move(y=-1); self.dir = 6
	def moveDown(self):  self.move(y= 1); self.dir = 2
	def moveLeft(self):  self.move(x=-1); self.dir = 4
	def moveRight(self): self.move(x= 1); self.dir = 0
	def turnLeft(self):  self.turn(self.dir-1 - 1*(not self.allowDiagonal))
	def turnRight(self): self.turn(self.dir+1 + 1*(not self.allowDiagonal))

class Interface():
	c_squareSize = 32#size of each square in pixels
	c_palette = ((255, 215, 175),#0 - ground
	             (0, 0, 0),#1 - wall
	             (50, 120, 200),#2 - friendly
	             (200, 40, 60),#3 - enemy
	             (200, 130, 40))#4 - mine
	c_palMax = len(c_palette)-1 -1#disables hazards
	c_colorBerserker = (50, 200, 50)
	c_guiBG = (35, 35, 35)
	c_guiField = ((28, 28, 28), (44, 44, 44), (20, 20, 20))#[0] == base, [1] == hover, [2] == selected
	c_guiText = (192, 192, 192)
	c_guiTextDamage = (255, 180, 80)
	c_guiTextError = (255, 100, 150)
	c_guiTextSuccess = (70, 220, 120)
	c_prevPath = (255, 0, 0)
	def __init__(self, map, berserker):
		self.damages = {}#[(x, y)] = int()
		self.map = map
		self.berserker = berserker
		self.berserker.executor.promptUser = self.promptUser#override
		self.berserker.executor.errorCallback = self.errorCallback#override
		
		
		
		self.prev_mclick = False
		self.prev_mclick2 = False
		self.prev_map_id = 0
	def run(self):
		#pygame init
		pygame.init()
		window = pygame.display.set_mode((self.map.width*self.c_squareSize + 400, max(self.map.height*self.c_squareSize, 400)))
		clock = pygame.time.Clock()
		self.pg_font = pygame.font.Font("profontwindows.ttf", 16)
		pygame.key.set_repeat(220, 60)#awesome
		self.window, self.clock = window, clock
		
		#gui setup/init:
		self.x_gui = self.map.width*self.c_squareSize# x offset for gui
		self.y_gui = 45# y offset for gui
		self.g_label_width = 260
		self.g_input_width = 135
		
		#add elements:
		#self.g_labels = ["HP", "MP", "SP", "ATT", "MAG", "MOV", "ACT", "RANGE"]
		self.g_labels = ["HP", "ATT", "MOV", "ACT", "RANGE", "Action limit"]
		self.g_inputs = []
		for i in xrange(len(self.g_labels)):
			self.g_inputs.append(eztext.Input(maxlength  = 10,
			                                  color      = self.c_guiText,
			                                  prompt     = "",
			                                  font       = self.pg_font,
			                                  x          = self.x_gui + self.g_label_width + 5,
			                                  y          = i*26 + 3 + self.y_gui,
			                                  restricted = "0123456789"))
			
			if self.g_labels[i] in ("ACT", "RANGE"): self.g_inputs[-1].value = "1"
			if self.g_labels[i] in ("MOV"): self.g_inputs[-1].value = "5"
			if self.g_labels[i] in ("Action limit"): self.g_inputs[-1].value = "10000"
		self.g_selected, self.g_hover = None, None
		self.g_labels.extend(["Clear path", "Clear damage", "View targeting", "spis meg", "Print register changes", "Load from scripts", "Load from clipboard", "Simulate turn", "Clear damage on turn"])
		self.g_buttons = [False for _ in xrange(len(self.g_labels) - len(self.g_inputs))]
		self.g_buttonLabel = [self.pg_font.render("False", False, self.c_guiText),
		                      self.pg_font.render("True" , False, self.c_guiText),
		                      self.pg_font.render("Submit" , False, self.c_guiText)]
		#render labels:
		self.g_texts = map(lambda x: self.pg_font.render(x + ":", False, self.c_guiText), self.g_labels)
		
		#button events:
		self.g_buttons[ 0] = self.clearPath
		self.g_buttons[ 1] = self.clearDamage
		self.g_buttons[ 2] = self.showTargetPattern
		self.g_buttons[-5] = self.printRegisterChanges
		self.g_buttons[-4] = self.setCodeFromScripts
		self.g_buttons[-3] = self.setCodeFromClipboard
		self.g_buttons[-2] = self.doTurn
		
		#Status updates:
		self.g_updates = []#i = (rendered text, timestamp)
		self.g_updates_y_offset = 0.#will move towards 0
		
		while 1:
			#events
			events = pygame.event.get()
			for event in events:
				if event.type == pygame.QUIT:
					sys.exit(0)
				elif event.type == pygame.KEYDOWN:
					if self.g_selected == None:
						if event.key == pygame.K_PAGEUP:
							self.berserker.moveForward()
						if event.key == pygame.K_PAGEDOWN:
							self.berserker.moveBackward()
						if event.key == pygame.K_HOME:
							self.berserker.attack()
						if event.key == pygame.K_UP:
							self.berserker.moveUp()
						if event.key == pygame.K_DOWN:
							self.berserker.moveDown()
						if event.key == pygame.K_LEFT:
							self.berserker.moveLeft()
						if event.key == pygame.K_RIGHT:
							self.berserker.moveRight()
						if event.key == pygame.K_COMMA:
							self.berserker.turnLeft()
						if event.key == pygame.K_PERIOD:
							self.berserker.turnRight()
			
			#step
			self.stepGUI(events)
			
			#draw
			window.fill(self.c_guiBG)
			self.draw(window)
			
			#fps
			clock.tick(60)
			
			#flip
			pygame.display.flip()
	def stepGUI(self, events):
		#get mouse:
		mx, my = pygame.mouse.get_pos()
		mclick = pygame.mouse.get_pressed()[0] == 1
		mclick2 = pygame.mouse.get_pressed()[2] == 1
		if mclick and self.prev_mclick:
			mclick = False
		else:
			self.prev_mclick = mclick
		if mclick2 and self.prev_mclick2:
			mclic2 = False
		else:
			self.prev_mclick2 = mclick2
		
		#step animations:
		self.g_updates_y_offset -= self.g_updates_y_offset / 10
		if self.g_updates and time.time() - self.g_updates[0][1] > 15:
			del self.g_updates[0]
		
		#gui mouse hover and click:
		#self.x_gui is x offset for gui
		self.g_hover = None
		if self.g_selected >= len(self.g_inputs):
			self.g_selected = None
		if self.x_gui + self.g_label_width <= mx < self.x_gui + self.g_label_width + self.g_input_width:
			if mclick:
				self.g_selected = None
			for i in xrange(len(self.g_texts)):
				if self.y_gui+26*i <= my < 24 + self.y_gui + 26*i:
					self.g_hover = i
					if mclick:
						if i >= len(self.g_inputs):#button
							j = i - len(self.g_inputs)
							self.g_selected = i
							if type(self.g_buttons[j]) is bool:
								self.g_buttons[j] = not self.g_buttons[j]
							else:
								self.g_buttons[j]()
							
						else:#input field
							self.g_selected = i
					break
			else:
				self.g_hover = None
		elif mclick:
			self.g_selected = None
		
		#gui text input
		if self.g_selected <> None and self.g_selected < len(self.g_inputs):
			self.g_inputs[self.g_selected].update(events)
		
		#do map controls:
		w, h, s = self.map.width, self.map.height, self.c_squareSize#speedup
		if 0 <= mx < s*w and 0 <= my <= s*h and (mclick or mclick2 or self.prev_mclick or self.prev_mclick2):
			x = mx // s
			y = my // s
			
			if mclick:
				i = self.map.get(x, y)
				i += 1
				if i > self.c_palMax:
					i = 0
				self.prev_map_id = i
			else:
				i = self.prev_map_id
			
			if x <> self.berserker.x or y <> self.berserker.y:
				self.map.set(x, y, i)
	def draw(self, surface):
		s = self.c_squareSize#speedup
		
		#draw gui
		for i, text in enumerate(self.g_texts):
			c = 0
			if i == self.g_selected:
				c = 2
			elif i == self.g_hover:
				c = 1
			
			surface.blit(text, (self.x_gui+self.g_label_width - text.get_width() - 5, i*26 + 3 + self.y_gui))
			pygame.draw.rect(surface, self.c_guiField[c], (self.x_gui + self.g_label_width, i*26 + self.y_gui, self.g_input_width, 24))
			if i < len(self.g_inputs):
				self.g_inputs[i].draw(surface)
			else:
				c = 2
				if type(self.g_buttons[i-len(self.g_inputs)]) is bool:
					c = 1 * self.g_buttons[i-len(self.g_inputs)]
				surface.blit(self.g_buttonLabel[c], (self.x_gui + self.g_label_width + self.g_input_width/2 - self.g_buttonLabel[c].get_width()/2, i*26+3 + self.y_gui))
		
		#draw board:
		for x in xrange(self.map.width):
			for y in xrange(self.map.height):
				pygame.draw.rect(surface, self.c_palette[self.map.get(x, y)], (x*s, y*s, s-1, s-1))
		
		#draw berserker.prevPath:
		if self.berserker.prevPath:
			pygame.draw.lines(surface, self.c_prevPath, False, tuple((x*s + s/2, y*s + s/2) for x, y in self.berserker.prevPath + [(self.berserker.x, self.berserker.y)]), 2)
		
		#draw berserker:
		pygame.draw.rect(surface, self.c_colorBerserker, (self.berserker.x*s, self.berserker.y*s, s-1, s-1))
		dir = self.berserker.dir2coord[self.berserker.dir]
		pygame.draw.line(surface, (0, 0, 0), (self.berserker.x*s + s/2, self.berserker.y*s + s/2), (self.berserker.x*s + s/2 + s/2 * dir[0], self.berserker.y*s + s/2 + s/2 * dir[1]))
		
		#draw damages:
		for (x, y), (damage, text) in self.map.damages.iteritems():
			if not text:
				#text = self.pg_font.render(str(damage), False, self.c_guiText)
				text = self.renderOutlined(str(damage), self.c_guiTextDamage, self.c_guiBG)
				self.map.damages[(x, y)][1] = text
			
			surface.blit(text, (x*s + s/2 - text.get_width()/2, y*s))
		
		#draw status updates:
		if self.g_updates: 
			th = self.g_updates[0][0].get_height()
			oy = self.map.height*self.c_squareSize - th + int(self.g_updates_y_offset) - 8
			for i, (text, timestamp) in enumerate(self.g_updates[::-1]):
				surface.blit(text, (8, oy - i*th))
	#events:
	def doTurn(self):
		if self.pushFieldToBerserker():
			self.clearPath()
			if self.g_buttons[-1]:
				self.clearDamage()
			self.statusUpdate("Start simulating turn...", color = self.c_guiTextSuccess)
			self.berserker.doTurn()
			return True
		return False
	def printRegisterChanges(self):
		register = self.promptListChoice([None] + [i[0] for i in self.berserker.executor.regnames if i[1]])
		self.berserker.executor.PrintRegisterChanges(register, lambda x: self.statusUpdate("%s set to %i" % (register, x)))
	def setCodeFromScripts(self):
		script = self.promptListChoice(sorted(map(lambda x: os.path.basename(x)[:-10], glob.glob("scripts/*.berserker")), key=lambda x: x.lower()))
		f = open("scripts/%s.berserker" % script, "r")
		self.setCodeFromClipboard(f.read())
		f.close()
	def setCodeFromClipboard(self, data=None):
		if not data: data = getClipboard()
		
		try:
			self.berserker.load(data)
		except ScripterBaseError as e:
			
			self.errorCallback("%s: %s" % (e.__class__.__name__, e))
		else:
			self.statusUpdate("Berserker code loaded", color = self.c_guiTextSuccess)
	def clearPath(self):
		if self.berserker.prevPath:
			self.berserker.prevPath = []
			self.statusUpdate("Path cleared")
	def clearDamage(self):
		if self.map.damages:
			del self.map.damages
			self.map.damages = {}
			self.statusUpdate("Damage cleared")
	def showTargetPattern(self):
		if self.pushFieldToBerserker():
			self.clearDamage()
			for i, (tx, ty) in enumerate(self.berserker.listTargets(all=True)):
				self.map.addDamage(tx, ty, i)
			self.statusUpdate("Target order printed")
			return True
		return False
	def statusUpdate(self, text, color=c_guiText):#WIP
		#todo: draw this somewhere
		print text
		
		self.g_updates.append((self.renderOutlined(text, c1=color, width=2), time.time()))
		#if len(self.g_updates) > 8:
		#	del self.g_updates[0]
		
		self.g_updates_y_offset += float(self.g_updates[-1][0].get_height())
	def errorCallback(self, text): self.statusUpdate(text, color=self.c_guiTextError)
	def promptUser(self, prompt):#WIP
		print "Interface prompt:\n\t",
		return self.berserker.executor.promptUser(prompt)
	#helpers:
	def promptListChoice(self, alternatives):
		choices = []
		for i in alternatives:
			choices.append((self.renderOutlined(str(i), width=1), i))
		
		if choices:
			window, clock = self.window, self.clock
			w = max([i[0].get_width() for i in choices]) + 8
			h = 25 * len(choices)
			ox, oy = self.map.width*self.c_squareSize - w - 20, 10
			self.prev_mclick = False
			
			while 1:
				#events
				events = pygame.event.get()
				for event in events:
					if event.type == pygame.QUIT:
						return
				
				mx, my = pygame.mouse.get_pos()
				mclick = pygame.mouse.get_pressed()[0] == 1
				if mclick and self.prev_mclick:
					mclick = False
				else:
					self.prev_mclick = mclick
				
				
				#draw bg:
				window.fill(self.c_guiBG)
				self.draw(window)
				
				#step and draw list:
				pygame.draw.rect(window, self.c_guiBG, (ox, oy, w + 10, h + 10))#could be larger than window....
				for i, (text, value) in enumerate(choices):
					c = 0
					if ox + 5 <= mx < ox + w+5 and oy + 5+25*i <= my < oy + 29+25*i:
						c = 1 + 1*mclick
						if mclick:
							#makes it feel more responsive:
							self.prev_mclick = False
							window.fill(self.c_guiBG)
							self.draw(window)
							pygame.display.flip()
							
							#"fixes" the problem of the user changing the stage when the prompt goes away
							time.sleep(0.2)
							
							return value
					
					pygame.draw.rect(window, self.c_guiField[c], (ox + 5, oy + i*25 + 5, w, 24))
					#window.blit(text, (ox + 5+w/2 - text.get_width()/2, 5+i*25 + oy))
					window.blit(text, (ox + 8, 5+i*25 + oy))
				
				
				#fps
				clock.tick(60)
				
				#flip
				pygame.display.flip()
	def renderOutlined(self, text, c1=c_guiText, c2=c_guiBG, width = 1):
		t1 = self.pg_font.render(text, False, c1)
		t2 = self.pg_font.render(text, False, c2)
		ret = pygame.surface.Surface((t1.get_width()+width*2, t1.get_height()+width*2)).convert()
		ret.set_colorkey((255, 0, 220))
		ret.fill((255, 0, 220))
		
		for x in xrange(width*2+1):
			for y in xrange(width*2+1):
				if (x-width)**2 + (y-width)**2 <= width**2:
					ret.blit(t2, (x, y))
		
		ret.blit(t1, (width, width))
		
		return ret
	def pushFieldToBerserker(self):
		for i in self.g_inputs:
			if not i.value:
				i.value = "0"
		try:
			self.berserker.HP.value  = int(self.g_inputs[self.g_labels.index("HP")].value)
			#self.berserker.MP.value  = int(self.g_inputs[self.g_labels.index("MP")].value)
			#self.berserker.SP.value  = int(self.g_inputs[self.g_labels.index("SP")].value)
			self.berserker.ATT.value = int(self.g_inputs[self.g_labels.index("ATT")].value)
			#self.berserker.MAG.value = int(self.g_inputs[self.g_labels.index("MAG")].value)
			self.berserker.MOV.value = int(self.g_inputs[self.g_labels.index("MOV")].value)
			self.berserker.ACT.value = int(self.g_inputs[self.g_labels.index("ACT")].value)
			self.berserker.RANGE.value = int(self.g_inputs[self.g_labels.index("RANGE")].value)
			
			self.berserker.executor.actionLimit = int(self.g_inputs[self.g_labels.index("Action limit")].value)
		except ValueError:
			self.errorCallback("Error: Invalid stats!")
			return False
		
		return True

def main(argv):#takes cli parameters backwards
	size = 18#normal go board size
	
	#handle parameters:
	if argv:
		output = None
		close = False
		
		while argv:
			i = argv.pop()
			if i[0] <> "-" or i[-1] == "-":
				print "Invalid input parameters"
				sys.exit(1)
			while i[0] == "-": i = i[1:]
			
			if i in ("h", "help"):
				print "== usage: ehc.py <[parameters]> =="
				print ""
				print "Parser:"
				
				print "\t-p, --parse [input]"
				print "\t\t[input] can be a filepath, the data or \"-\" for stdin. the result will be printed"
				
				print "\t-o, --output [output]"
				print "\t\tWrites the output to [output] filepath as well"
				
				print "Simulator:"
				
				print "\t-s, --size [number]"
				print "\t\tSets the board  size to [number] x [number]"
				
				sys.exit(0)
			elif i in ("p", "parse"):
				source = argv.pop()
				if source == "-":
					data = sys.stdin.read()
				elif os.path.isfile(source):
					with open(source) as f:
						data = f.read()
				else:
					data = source
				
				parser = Script()
				parser.loadSource(data)
				out = parser.getBytecode()
				print out
				
				close = True
			elif i in ("o", "output"):
				assert output
				
				with open(argv.pop(), "w") as f:
					f.write(output)
			elif i in ("s", "size"):
				size = int(argv.pop())
				assert size > 0
				
		if close:
			sys.exit(0)
	
	map = Map(size, size)
	berserker = Berserker((size/2, size/2), map)
	gui = Interface(map, berserker)
	gui.run()
	
if __name__ == "__main__":
	main(sys.argv[1:][::-1])








