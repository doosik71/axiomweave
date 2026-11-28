# AxiomWeave 언어 명세 (Language Specification)

> **문서 상태:** 초안(Draft) · 단편 L0, L1, L2와 단계 L3 · 대상 버전 v0.1 (L1: [§12](#12-단편-l1-dsl), L2: [§13](#13-단편-l2-dsl), L3: [§14](#14-단계-l3-dsl-자연수))  
> 상위 문서: [specification.md](specification.md), 논리 규칙: [logic-spec.md](logic-spec.md). 이 문서는 v0.1 Python 임베디드 DSL의 표면 문법, 선언과 증명 작성 방식, 커널 입력으로의 변환(Elaboration)을 정의한다. 규범적 표현은 [specification.md §1.1](specification.md#11-규범적-표현)을 따른다.

## 1. 범위

| 포함                                              | 제외                                                            |
| ------------------------------------------------- | --------------------------------------------------------------- |
| L0 명제의 Python 표현 (`Prop`, 연산자, 생성 함수) | `ForAll`, `Exists`, `Real`, `Symbol` 등 L1 이후 구성 요소       |
| `Theory` 객체를 통한 공리·정리·증명 선언          | 독립 `.axw` 문법과 파서                                         |
| 증명 문맥(`ctx`)의 목표 전술과 전방 추론 연산     | `rewrite`, `unfold`, `induction`, `ring`, `linarith`, `auto` 등 |
| Elaboration 규칙과 검증 상태 전이                 | 증명 객체·인증서의 인코딩 (`kernel-spec.md`)                    |
| 진단 메시지와 예외 분류                           | 외부 백엔드, AxiomAI, Jupyter·IDE 연계                          |

README §4와 `proposal.md` §5의 예제 중 이 문서와 다른 부분은 설계 방향을 보여주는 비규범적 예시이다. v0.1 동작은 이 문서를 따른다.

## 2. 설계 결정 요약

| 항목           | 결정                                                                                        |
| -------------- | ------------------------------------------------------------------------------------------- |
| 신뢰 수준      | DSL 전체는 비신뢰 계층이다. DSL이 무엇을 하든 최종 판정은 커널이 한다.                      |
| 환경 노출      | 명시적 `Theory` 객체를 사용한다. 전역 정리 레지스트리를 두지 않는다.                        |
| 증명 작성 방식 | 혼합형. 목표 기반 전술과, 사실(`Fact`)을 조합하는 전방 추론 연산을 함께 제공한다.           |
| 검증 시점      | 데코레이터는 등록만 한다. `Theory.check()` 또는 `axw check` 호출 시 선언 순서대로 검증한다. |
| 함의 연산자    | `>>`를 유지하되 괄호 사용을 규정하고, 우결합 가변 인자 `Implies(A, B, C, …)`를 제공한다.    |
| 축약 표기      | `Not`, `Truth`, `Iff`, `~`는 생성 시점에 원시 연산자로 전개된 `Prop`을 반환한다.            |
| 명제의 `==`    | 구조적 동일성(bool)이다. 수학적 등식은 L2의 `Eq()`로만 표현한다.                            |

## 3. 신뢰 경계

- DSL, Elaborator, 전술은 [specification.md §5.4](specification.md#54-신뢰-기반)의 비신뢰 구성 요소이다.
- DSL의 검사(타입 오류, 목표 불일치, 가정 범위 오류 등)는 사용성을 위한 조기 진단이며, 커널 검사를 대체해서는 안 된다.
- 정리의 상태를 `VERIFIED`로 바꿀 수 있는 것은 커널의 수락 결과뿐이어야 한다. Elaborator의 성공만으로 `VERIFIED`가 되어서는 안 된다.
- 정리 선언 함수와 증명 함수는 일반 Python 코드로 실행된다. `axw check`로 파일을 검사하는 것은 그 파일의 코드를 실행하는 것이므로, 신뢰할 수 없는 파일은 인증서(`.axwp`)로만 받아 `axw verify`로 검증하는 것을 권장한다.

## 4. 명제

### 4.1. `Prop` 객체

`Prop`은 L0 명제([logic-spec.md §3.4](logic-spec.md#34-항))를 나타내는 Python 클래스이다.

- `Prop` 객체는 불변이어야 하며 해시 가능해야 한다.
- `Prop` 객체의 구조는 원자, `Falsehood`, 또는 원시 연산자(`and`, `or`, `imp`)를 두 `Prop`에 적용한 트리뿐이어야 한다.
- `Prop` 객체는 축약 표기 노드를 포함해서는 안 된다 ([4.4](#44-축약-표기)).

### 4.2. 원자와 상수

| API                 | 의미                      |
| ------------------- | ------------------------- |
| `Prop.symbol(name)` | 이름이 `name`인 명제 원자 |
| `Falsehood`         | 거짓 명제 $\bot$          |

```python
from axiomweave import Prop

P, Q, R = (Prop.symbol(name) for name in ("P", "Q", "R"))
```

- 원자는 이름으로 식별된다. 같은 이름으로 만든 원자는 어느 모듈에서 만들었든 같은 원자이다 (`Prop.symbol("P") == Prop.symbol("P")`).
- 원자 이름은 Python 식별자 형식(`[A-Za-z_][A-Za-z0-9_]*`)이어야 하며, 예약어 `and`, `or`, `imp`, `false`일 수 없다. 이 규칙은 [kernel-spec.md §3](kernel-spec.md#3-이름-구문)의 이름 구문과 같다.
- 잘못된 이름은 생성 시점에 `AxwTypeError`를 일으켜야 한다.

### 4.3. 생성 함수와 연산자

| 논리                     | 생성 함수            | 연산자   | 결과 구조                                                        |
| ------------------------ | -------------------- | -------- | ---------------------------------------------------------------- |
| $A \land B$              | `And(A, B)`          | `A & B`  | $\mathsf{and}\ A\ B$                                             |
| $A \lor B$               | `Or(A, B)`           | `A \| B` | $\mathsf{or}\ A\ B$                                              |
| $A \to B$                | `Implies(A, B)`      | `A >> B` | $\mathsf{imp}\ A\ B$                                             |
| $A_1 \to \ldots \to A_n$ | `Implies(A₁, …, Aₙ)` | —        | $\mathsf{imp}\ A_1\ (\mathsf{imp}\ A_2\ (\ldots\ A_n))$ (우결합) |
| $\lnot A$                | `Not(A)`             | `~A`     | $\mathsf{imp}\ A\ \bot$                                          |
| $\top$                   | `Truth`              | —        | $\mathsf{imp}\ \bot\ \bot$                                       |
| $A \leftrightarrow B$    | `Iff(A, B)`          | —        | $\mathsf{and}\ (\mathsf{imp}\ A\ B)\ (\mathsf{imp}\ B\ A)$       |

- `And`, `Or`, `Iff`는 정확히 두 인자를 받아야 한다. `Implies`는 두 개 이상의 인자를 받아야 한다.
- 모든 인자와 피연산자는 `Prop`이어야 한다. Python `bool`, 숫자, 문자열 등은 자동 변환하지 않으며 `AxwTypeError`(또는 연산자의 경우 Python 기본 `TypeError`)를 일으켜야 한다. 특히 `True`/`False`를 `Truth`/`Falsehood`로 변환해서는 안 된다.
- `P & Q & R`은 Python 규칙에 따라 `(P & Q) & R`로 구성된다. 커널은 결합법칙을 사용하지 않으므로 `P & (Q & R)`과 다른 명제이다.

### 4.4. 축약 표기

`Not`, `~`, `Truth`, `Iff`는 생성 시점에 [logic-spec.md §4](logic-spec.md#4-축약-표기)의 전개 결과를 반환해야 한다.

```python
assert Not(P) == Implies(P, Falsehood)
assert ~~P == Implies(Implies(P, Falsehood), Falsehood)
```

따라서 축약 표기는 커널에 도달하지 않는다.

### 4.5. 연산자 우선순위와 괄호 규칙

Python의 연산자 우선순위는 `~` > `>>` > `&` > `|` 이며, 이항 연산자는 모두 좌결합이다. 이는 논리 표기 관례([logic-spec.md §3.5](logic-spec.md#35-표기-규약): $\land$ > $\lor$ > $\to$, $\to$ 우결합)와 다르다.

| 작성한 코드   | Python이 구성하는 명제 | 의도했을 가능성이 높은 명제 |
| ------------- | ---------------------- | --------------------------- |
| `P >> Q >> R` | $(P \to Q) \to R$      | $P \to (Q \to R)$           |
| `P & Q >> R`  | $P \land (Q \to R)$    | $(P \land Q) \to R$         |
| `P >> Q \| R` | $(P \to Q) \lor R$     | $P \to (Q \lor R)$          |

런타임에서는 괄호가 있었는지 구분할 수 없으므로 DSL은 위 차이를 검출할 수 없다. 사용자 코드는 다음 규칙을 따라야 한다.

1. `>>`를 연쇄해서는 안 된다. 연쇄 함의는 `Implies(A, B, C)` 또는 명시적 괄호 `A >> (B >> C)`로 작성한다.
2. 서로 다른 이항 연산자(`&`, `|`, `>>`)를 섞을 때는 모든 하위 식에 괄호를 써야 한다.
3. `~`는 원자나 괄호로 묶인 식에만 붙이는 것을 권장한다 (`~P`, `~(P & Q)`).

이 규칙의 정적 검출(린트)은 후속 도구에서 제공한다. 규칙을 어긴 코드도 명제는 구성되며, 의도와 다른 명제는 결론 불일치로 증명 단계에서 드러난다.

### 4.6. Python 진릿값 및 비교

- `Prop.__bool__`은 `AxwTypeError`를 일으켜야 한다. 따라서 `if P:`, `P and Q`, `P or Q`, `not P`는 모두 오류이다.
- `A == B`는 두 명제의 구조적 동일성([logic-spec.md §3.6](logic-spec.md#36-항의-동등성))을 `bool`로 반환한다. 이는 Python 객체 비교이며 수학적 명제를 만들지 않는다.
- `<`, `<=`, `>`, `>=`는 `Prop`에 정의하지 않는다.

### 4.7. 표시

- `str(A)`는 원시 연산자만 사용한 유니코드 표기(`∧`, `∨`, `→`, `⊥`)를 [logic-spec.md §3.5](logic-spec.md#35-표기-규약)의 우선순위에 따라 최소 괄호로 출력해야 한다. v0.1은 $A \to \bot$를 $\lnot A$로 다시 접어 표시하지 않는다.
- `repr(A)`는 평가하면 같은 명제를 만드는 생성 함수 형식(예: `Implies(Prop.symbol('P'), Falsehood)`)을 출력하는 것을 권장한다.

## 5. Theory

### 5.1. 생성

```python
from axiomweave import Theory

thy = Theory("demo.logic", imports=[])
```

| 매개변수  | 의미                                                      |
| --------- | --------------------------------------------------------- |
| `name`    | 점으로 구분된 식별자. 선언의 정규 이름 접두사로 사용된다. |
| `imports` | 이 Theory보다 앞에 놓이는 다른 `Theory` 객체들의 목록     |

- `Theory`의 선언 목록은 가져온 Theory의 선언들(가져온 순서, 전이적 포함, 같은 객체는 한 번만)과 이 Theory의 선언들(선언 순서)을 이어 붙인 것이다.
- 커널에 전달되는 [logic-spec.md §7](logic-spec.md#7-환경)의 환경은 이 선언 목록에서 공리와 `VERIFIED` 정리만 순서대로 포함한다. `VERIFIED`가 아닌 정리는 환경에 들어가지 않으므로, 이를 참조하는 증명은 커널에서 거부된다.
- 선언의 정규 이름은 `"<theory name>.<declaration name>"`이다. 환경 안에서 정규 이름이 중복되면 `DeclarationError`를 일으켜야 한다.
- 전역 기본 Theory는 제공하지 않는다.

### 5.2. 공리 선언

```python
@thy.axiom
def my_axiom() -> Prop:
    return P >> P
```

- `@thy.axiom`은 함수를 즉시 한 번 호출하여 반환된 `Prop`을 공리 스키마로 등록하고, `Axiom` 핸들을 반환한다.
- 함수는 매개변수를 받아서는 안 되며 `Prop`을 반환해야 한다. 위반 시 `DeclarationError`를 일으켜야 한다.
- 명제의 원자는 스키마 변수이다 ([logic-spec.md §7.1](logic-spec.md#71-선언)).
- 공리는 검증 시 허용 목록에 있어야 한다 ([5.6](#56-검증)).

### 5.3. 정리 선언

```python
@thy.theorem
def imp_self() -> Prop:
    return P >> P
```

- `@thy.theorem`은 함수를 즉시 한 번 호출하여 반환된 `Prop`을 정리의 명제로 등록하고, `Theorem` 핸들을 반환한다.
- 함수는 매개변수를 받아서는 안 되며 `Prop`을 반환해야 한다. 매개변수를 받는 정리 선언(README §4.3)은 전칭 양화가 필요하므로 L1 이후에 정의한다.
- 선언 순서는 `@thy.theorem`/`@thy.axiom`이 적용된 순서이다. 이 순서가 환경의 순서이며, 정리는 자신보다 앞선 선언만 사용할 수 있다.
- 정리 선언 함수를 실행하는 것은 명제를 만드는 일일 뿐이며, 증명이나 검증을 수행하지 않는다.

### 5.4. 증명 등록

```python
@thy.proof(imp_self)
def _(ctx):
    hp = ctx.intro()
    ctx.exact(hp)
```

- `@thy.proof(theorem)`은 증명 함수를 `theorem`에 등록만 하고, 함수를 실행하지 않는다. 데코레이터는 원래 함수를 그대로 반환한다.
- `theorem`은 같은 Theory에 선언된 `Theorem`이어야 한다. 한 정리에 증명을 두 번 등록하면 `DeclarationError`를 일으켜야 한다.
- 증명 함수는 증명 문맥 하나를 인자로 받고, 반환값은 무시된다.
- 증명 등록 위치는 환경의 순서에 영향을 주지 않는다. 사용할 수 있는 정리는 정리 선언의 순서로 결정된다.

### 5.5. 핸들

| 핸들      | 주요 속성                                                           |
| --------- | ------------------------------------------------------------------- |
| `Theorem` | `name`(정규 이름), `statement`(`Prop`), `status`, `axioms`(검증 후) |
| `Axiom`   | `name`, `statement`                                                 |

- `Theorem.status`의 초기값은 `UNPROVEN`이며, [5.7](#57-검증-상태-전이)에 따라서만 바뀐다.
- `Theorem.axioms`는 커널이 계산한 의존 공리의 정규 이름 집합이다 ([logic-spec.md §8.4](logic-spec.md#84-공리-의존성)). 검증 전에는 `None`이다.

### 5.6. 검증

```python
report = thy.check(allowed_axioms=None)
```

- `check()`는 가져온 Theory를 먼저 검증한 뒤(이미 검증된 Theory는 다시 검증하지 않을 수 있다), 이 Theory의 정리들을 선언 순서대로 처리한다. v0.1 구현은 가져온 Theory의 정리까지 환경 전체를 매번 하나의 번들로 다시 검증하며, 그 정리들의 상태도 갱신한다.
- 각 정리에 대해 증명 함수를 실행하여 증명 객체를 만든다(Elaboration, [7](#7-elaboration)). 그런 다음 공리와 Elaboration에 성공한 정리들로 인증서 번들([kernel-spec.md §6](kernel-spec.md#6-인증서-번들))을 구성하고, 그 직렬화 바이트를 커널 진입점 `check_bundle`에 전달한다 ([kernel-spec.md §8.1](kernel-spec.md#81-진입점)). 번들의 선언 해시와 `axioms` 필드는 Elaborator가 채우며, 커널이 다시 계산하여 확인한다.
- `allowed_axioms`는 허용 공리 정규 이름의 집합이다. `None`이면 표준 허용 목록 `STANDARD_AXIOMS = {"classical.em"}`을 사용한다 ([logic-spec.md §8.3](logic-spec.md#83-공리-허용-정책), [§9](logic-spec.md#9-고전-원리)). Elaborator는 이 이름 집합을 이름→선언 해시 사상으로 바꾸어 커널에 명시적으로 전달해야 한다. 표준 이름은 커널에 내장된 표준 해시로, 그 밖의 이름은 이 Theory에 선언된 공리의 해시로 대응시킨다 ([kernel-spec.md §9](kernel-spec.md#9-허용-공리-정책)).
- 환경에 허용되지 않은 공리가 있으면 환경 전체를 거부해야 한다. 이때 어떤 정리도 커널 검사를 받지 않으며, Elaboration에 성공한 모든 정리는 `REJECTED`(진단 단계 `environment`)가 된다. 증명이 없거나 Elaboration 단계에서 멈춘 정리는 [5.7](#57-검증-상태-전이)의 상태를 유지한다.
- `check()`는 예외를 일으키지 않고 `CheckReport`를 반환한다. 단, API 오용은 예외를 일으킨다. `allowed_axioms`에 문자열 하나를 넘기면 `AxwTypeError`, 표준 목록에도 환경에도 없는 공리 이름을 넘기면 `DeclarationError`가 발생한다.
- `check()`는 매번 전체 Theory를 다시 처리한다. v0.1은 검증 결과 캐싱을 요구하지 않는다.
- v0.1의 `check()`는 커널을 같은 프로세스에서 실행할 수 있다. 별도 프로세스의 독립 재검증은 인증서와 `axw verify`로 수행한다 ([8](#8-인증서와-명령행)).

`CheckReport`는 다음을 제공해야 한다.

| 속성/메서드 | 의미                                                                        |
| ----------- | --------------------------------------------------------------------------- |
| `ok`        | 모든 정리가 `VERIFIED`이면 `True`                                           |
| `results`   | 정리별 상태, 진단 목록, 의존 공리 (가져온 Theory의 정리를 포함한 환경 순서) |
| `__str__`   | 사람이 읽을 수 있는 요약                                                    |

### 5.7. 검증 상태 전이

| 상황                                                    | 상태       | 진단 단계   |
| ------------------------------------------------------- | ---------- | ----------- |
| 증명 함수가 등록되지 않음                               | `UNPROVEN` | —           |
| 증명 함수가 정상 종료했으나 닫히지 않은 목표가 남음     | `UNPROVEN` | elaboration |
| 증명 함수 실행 중 `AxwError` 또는 기타 Python 예외 발생 | `REJECTED` | elaboration |
| 증명 객체를 커널이 거부                                 | `REJECTED` | kernel      |
| 허용되지 않은 공리로 환경이 거부됨                      | `REJECTED` | environment |
| 증명 객체를 커널이 수락                                 | `VERIFIED` | —           |

- 앞선 정리가 `VERIFIED`가 아닌데 뒤의 증명이 그 정리를 사용하면, 뒤의 정리는 `REJECTED`가 되어야 한다 ([specification.md §5.5](specification.md#55-언어)).
- `check()`를 다시 호출하면 모든 상태를 다시 계산한다.

## 6. 증명 문맥

### 6.1. 개념

| 개념        | 의미                                                                                 |
| ----------- | ------------------------------------------------------------------------------------ |
| 목표 (Goal) | 증명해야 할 명제와, 그 목표에서 사용할 수 있는 가정들의 문맥 $\Gamma$                |
| 목표 목록   | 아직 닫히지 않은 목표들의 순서 목록. 처음에는 정리의 명제 하나이며 문맥은 비어 있다. |
| 현재 목표   | 목표 목록의 첫 번째 목표. 목표 전술은 항상 현재 목표에 작용한다.                     |
| 사실 (Fact) | 어떤 문맥에서 도출된 명제를 나타내는 핸들. `fact.prop`으로 명제를 얻는다.            |

- `Fact`는 그것이 만들어진 문맥의 가정에만 의존한다. 현재 목표의 문맥이 그 가정들을 모두 포함할 때만 `Fact`를 사용할 수 있으며, 그렇지 않으면 `ScopeError`를 일으켜야 한다.
- 전방 추론 연산은 가정을 해제하지 않으므로, 이 조건을 만족하는 `Fact`의 도출은 현재 목표의 문맥에서도 유효하다 (약화, [logic-spec.md §10](logic-spec.md#10-메타-성질)).
- 목표 목록이 비어 있을 때 목표 전술을 호출하면 `TacticError`를 일으켜야 한다.

### 6.2. 가정 이름

- `intro`, `cases`가 도입하는 가정은 이름을 가진다. 이름을 주지 않으면 Elaborator가 결정적 규칙으로 신선한 이름(`h1`, `h2`, …)을 생성해야 한다.
- 한 증명 안에서 가정 이름은 모두 달라야 하며, 중복되면 `TacticError`를 일으켜야 한다. 이는 [logic-spec.md §8.2](logic-spec.md#82-가정-이름-규칙)보다 엄격한 규칙으로, `Fact`의 범위 판정을 단순하게 하기 위한 것이다.
- 가정 이름은 원자 이름과 같은 형식 규칙([4.2](#42-원자와-상수))을 따른다.

### 6.3. 목표 전술

| 전술                       | 현재 목표 ($\Gamma \vdash \cdot$)                   | 결과                                                                                                               |
| -------------------------- | --------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------ |
| `ctx.intro(name=None)`     | $A \to B$                                           | 목표를 $\Gamma, h : A \vdash B$로 바꾸고 가정 $h$의 `Fact`를 반환                                                  |
| `ctx.split()`              | $A \land B$                                         | 목표를 $\Gamma \vdash A$, $\Gamma \vdash B$ 두 개로 바꿈 (이 순서)                                                 |
| `ctx.left()`               | $A \lor B$                                          | 목표를 $\Gamma \vdash A$로 바꿈                                                                                    |
| `ctx.right()`              | $A \lor B$                                          | 목표를 $\Gamma \vdash B$로 바꿈                                                                                    |
| `ctx.cases(f, names=None)` | 임의의 $C$, $f : A \lor B$                          | 목표를 $\Gamma, h_1 : A \vdash C$, $\Gamma, h_2 : B \vdash C$ 두 개로 바꾸고 ($h_1$의 `Fact`, $h_2$의 `Fact`) 반환 |
| `ctx.exfalso()`            | 임의의 $A$                                          | 목표를 $\Gamma \vdash \bot$로 바꿈                                                                                 |
| `ctx.apply(f)`             | $B$, $f : A_1 \to \ldots \to A_n \to B$ ($n \ge 1$) | 목표를 $\Gamma \vdash A_1$, …, $\Gamma \vdash A_n$로 바꿈                                                          |
| `ctx.exact(f)`             | $A$, `f.prop == A`                                  | 현재 목표를 닫음                                                                                                   |
| `ctx.assumption()`         | $A$                                                 | $\Gamma$에 $A$와 같은 가정이 있으면 가장 최근의 것으로 목표를 닫음                                                 |
| `ctx.have(A, name=None)`   | 임의의 $B$                                          | 목표를 $\Gamma \vdash A$, $\Gamma, h : A \vdash B$ 두 개로 바꾸고 가정 $h$의 `Fact`를 반환                         |

- 현재 목표의 형태가 표의 조건과 맞지 않으면 `TacticError`를 일으켜야 한다.
- `apply`는 `f.prop`을 오른쪽으로 펼쳐 결론이 현재 목표와 같아지는 가장 짧은 $n$을 사용한다. 그런 $n$이 없으면 `TacticError`를 일으켜야 한다.
- `have`가 반환한 `Fact`는 두 번째 목표(및 그로부터 파생된 목표)에서만 유효하다.

### 6.4. 전방 추론 연산

다음 연산은 목표 목록을 바꾸지 않고 새 `Fact`를 반환한다. 결과 `Fact`의 문맥은 인자 `Fact`들의 문맥 중 가장 큰 것이며, 인자들의 문맥이 서로 포함 관계가 아니면 `ScopeError`를 일으켜야 한다.

| 연산                        | 인자                            | 결과                              |
| --------------------------- | ------------------------------- | --------------------------------- |
| `ctx.mp(f, g)`              | $f : A \to B$, $g : A$          | $B$                               |
| `ctx.and_intro(f, g)`       | $f : A$, $g : B$                | $A \land B$                       |
| `ctx.and_left(f)`           | $f : A \land B$                 | $A$                               |
| `ctx.and_right(f)`          | $f : A \land B$                 | $B$                               |
| `ctx.or_inl(f, B)`          | $f : A$, $B : \texttt{Prop}$    | $A \lor B$                        |
| `ctx.or_inr(A, f)`          | $A : \texttt{Prop}$, $f : B$    | $A \lor B$                        |
| `ctx.absurd(f, A)`          | $f : \bot$, $A : \texttt{Prop}$ | $A$                               |
| `ctx.thm(decl, subst=None)` | `Theorem` 또는 `Axiom`, 치환    | $\texttt{decl.statement}[\sigma]$ |

- 인자의 명제 형태가 맞지 않으면 `TacticError`를 일으켜야 한다.
- `ctx.thm`의 `subst`는 원자 `Prop`을 키로, `Prop`을 값으로 하는 `dict`이다. 예: `ctx.thm(and_comm, {P: A | B, Q: C})`. 키가 원자가 아니거나 `decl.statement`에 없는 원자이면 `TacticError`를 일으켜야 한다 ([logic-spec.md §6.3](logic-spec.md#63-인스턴스화-조건)).
- `ctx.thm`의 `decl`은 현재 정리보다 앞서 선언된 것이어야 하며, 그렇지 않으면 `DeclarationError`를 일으켜야 한다.
- `ctx.thm`이 만드는 `Fact`는 빈 문맥에 의존하므로 어느 목표에서나 사용할 수 있다.

### 6.5. 목표 구조화

```python
with ctx.focus():
    ...
```

- `ctx.focus()`는 블록에 들어갈 때의 현재 목표를 대상으로 하며, 블록이 끝날 때 그 목표와 그로부터 파생된 목표가 모두 닫혀 있지 않으면 `TacticError`를 일으켜야 한다.
- 블록 안의 전술은 대상 목표에서 파생된 목표에만 작용해야 한다.
- 여러 목표를 만드는 전술(`split`, `cases`, `apply`, `have`) 다음에는 각 목표를 `focus` 블록으로 감싸는 것을 권장한다.

### 6.6. 증명 상태 조회

| API         | 의미                                                        |
| ----------- | ----------------------------------------------------------- |
| `ctx.goals` | 현재 목표 목록 (각 목표의 문맥과 명제를 읽기 전용으로 제공) |
| `str(ctx)`  | 목표 목록의 사람이 읽을 수 있는 표시                        |

`str(ctx)`의 형식은 다음을 권장한다.

```text
goal 1/2
  h1 : P → Q
  h2 : P
  ⊢ Q
```

`ctx.goals`는 AxiomAI 등 자동화 도구가 사용하는 구조화된 상태이므로, 같은 증명 진행에 대해 결정적이어야 한다.

## 7. Elaboration

Elaboration은 증명 함수의 실행 기록을 [logic-spec.md §8](logic-spec.md#8-추론-규칙)의 도출로 변환하는 과정이다.

### 7.1. 대응 규칙

| DSL 연산                | 생성되는 규칙 적용                                                              |
| ----------------------- | ------------------------------------------------------------------------------- |
| `intro`                 | $\to\mathrm{I}$ (가정 이름, 가정 명제 $A$)                                      |
| 가정 `Fact`의 사용      | $\mathrm{Hyp}$ (가정 이름)                                                      |
| `split`, `and_intro`    | $\land\mathrm{I}$                                                               |
| `and_left`, `and_right` | $\land\mathrm{E}_1$, $\land\mathrm{E}_2$                                        |
| `left`, `or_inl`        | $\lor\mathrm{I}_1$ (추가되는 오른쪽 명제)                                       |
| `right`, `or_inr`       | $\lor\mathrm{I}_2$ (추가되는 왼쪽 명제)                                         |
| `cases`                 | $\lor\mathrm{E}$ (가정 이름 $h_1$, $h_2$)                                       |
| `exfalso`, `absurd`     | $\bot\mathrm{E}$ (결론 명제)                                                    |
| `mp`                    | $\to\mathrm{E}$                                                                 |
| `apply` ($n$개 전제)    | $\to\mathrm{E}$를 $n$번                                                         |
| `have A`                | $\to\mathrm{E}$ ($\to\mathrm{I}$ ($h : A$)로 만든 $A \to B$의 도출, $A$의 도출) |
| `thm` (정리)            | $\mathrm{Thm}$ (정규 이름, 치환)                                                |
| `thm` (공리)            | $\mathrm{Ax}$ (정규 이름, 치환)                                                 |
| `exact`, `assumption`   | 새 규칙 없음. `Fact`의 도출 또는 $\mathrm{Hyp}$을 목표 자리에 연결              |

- 위 표 외의 규칙 적용을 생성해서는 안 된다.
- 생성한 도출은 커널이 결론을 재계산할 수 있도록 [logic-spec.md §8.5](logic-spec.md#85-결론-재계산에-필요한-정보-참고)의 정보를 포함해야 한다.
- 같은 증명 함수와 같은 Theory에 대해 Elaboration은 같은 증명 객체를 만들어야 한다. 자동 생성 가정 이름도 결정적이어야 한다.

### 7.2. 완료 조건

증명 함수가 반환된 뒤 목표 목록이 비어 있으면 Elaborator는 도출을 증명 객체로 만들어 커널에 전달한다. 목표가 남아 있으면 커널에 전달하지 않고 정리를 `UNPROVEN`으로 둔다 ([5.7](#57-검증-상태-전이)).

## 8. 인증서와 명령행

- `thy.export(path)`는 이 Theory의 자기완결 인증서 번들을 `path`에 기록해야 한다. 번들은 가져온 Theory의 선언과 이 Theory의 공리 및 `VERIFIED` 정리를 포함한다. 인증서 형식은 [kernel-spec.md §6](kernel-spec.md#6-인증서-번들)에서 정의한다. 번들은 마지막 `check()`의 결과로 만들며, `check()`를 호출하기 전에 `export()`를 호출하면 `AxwError`가 발생한다.
- `axw check <file.py>`는 파일을 모듈로 가져와 모듈 최상위의 `Theory` 객체를 모두 찾아 `check()`를 수행하고, 모든 정리가 `VERIFIED`일 때만 종료 코드 0을 반환해야 한다. 다른 최상위 Theory가 가져온 Theory(예: `classical`)는 그 Theory의 검증에 포함되므로 따로 검사하지 않는다.
- `axw verify <file.axwp>`는 Python 증명 코드를 실행하지 않고 인증서만으로 커널 검증을 수행한다. 상세 동작은 [kernel-spec.md](kernel-spec.md)에서 정의한다.

## 9. 예외와 진단

| 예외               | 기반 클래스             | 발생 상황                                              |
| ------------------ | ----------------------- | ------------------------------------------------------ |
| `AxwError`         | `Exception`             | 모든 AxiomWeave 오류의 기반                            |
| `AxwTypeError`     | `AxwError`, `TypeError` | 잘못된 명제 구성, `Prop`의 진릿값 변환                 |
| `DeclarationError` | `AxwError`              | 잘못된 선언, 이름 중복, 증명 중복 등록, 선언 순서 위반 |
| `TacticError`      | `AxwError`              | 목표 형태 불일치, 가정 이름 중복, 닫히지 않은 `focus`  |
| `ScopeError`       | `AxwError`              | 범위를 벗어난 `Fact` 사용                              |

진단 정보는 최소한 다음을 포함해야 한다.

- 정리의 정규 이름과 진단 단계 (`elaboration`, `kernel`, `environment`)
- Elaboration 단계 오류의 경우, 오류가 발생한 증명 코드의 파일과 줄 번호
- 오류 시점의 목표 목록 ([6.6](#66-증명-상태-조회) 형식)
- 커널 단계 오류의 경우, 거부한 규칙 적용과 사유

## 10. 표준 Theory

v0.1 패키지는 AxiomLib의 표준 Theory로 `classical`(10.1)과 `propositional`(10.2)을 제공한다. 표준 산술 Theory `arith`는 [14.3](#143-표준-theory-arith)에서 정의한다. 표준 Theory는 일반 사용자 Theory와 같은 DSL로 작성하며, 다른 Theory와 마찬가지로 `check()`에서 커널이 검증한다. 표준 Theory라는 이유로 검증을 생략해서는 안 된다.

### 10.1. `classical`

v0.1 패키지는 [logic-spec.md §9](logic-spec.md#9-고전-원리)의 고전 원리를 담은 Theory를 제공해야 한다.

```python
from axiomweave.lib.logic.classical import classical, em, dne, peirce
```

| 핸들     | 종류      | 정규 이름          | 명제 (원자 `P`, `Q`)   |
| -------- | --------- | ------------------ | ---------------------- |
| `em`     | `Axiom`   | `classical.em`     | `P \| ~P`              |
| `dne`    | `Theorem` | `classical.dne`    | `~~P >> P`             |
| `peirce` | `Theorem` | `classical.peirce` | `((P >> Q) >> P) >> P` |

- `dne`와 `peirce`는 `em`으로부터 증명되어야 한다.
- 이 Theory를 가져오지 않은 Theory의 정리는 고전 원리에 의존할 수 없다.

### 10.2. `propositional`

v0.1 패키지는 직관주의 명제 논리의 기본 법칙을 담은 Theory를 제공해야 한다.

```python
from axiomweave.lib.logic.propositional import propositional, and_comm, iff_trans
```

- Theory 이름은 `propositional`이며, 아무 Theory도 가져오지 않고 공리를 선언하지 않는다. 따라서 모든 정리의 의존 공리 집합은 비어 있어야 한다.
- 정리의 명제는 원자 `P`, `Q`, `R`만 사용한다. 다른 명제에 쓰려면 `ctx.thm(and_comm, {P: A, Q: B})`처럼 치환한다 ([6.4](#64-전방-추론-연산)).
- 모듈은 아래 표의 각 정리를 같은 이름의 `Theorem` 핸들로 노출해야 하며, 선언 순서는 표의 순서이다. 뒤의 정리의 증명은 앞의 정리를 사용할 수 있다.
- 고전 원리가 필요한 법칙(예: $\lnot(P \land Q) \to \lnot P \lor \lnot Q$)은 이 Theory에 넣어서는 안 된다.

| 분류      | 핸들                | 명제 (DSL 표기)                             |
| --------- | ------------------- | ------------------------------------------- |
| 함의      | `imp_refl`          | `P >> P`                                    |
|           | `imp_const`         | `Implies(P, Q, P)`                          |
|           | `imp_trans`         | `Implies(P >> Q, Q >> R, P >> R)`           |
|           | `imp_swap`          | `Implies(P, Q, R) >> Implies(Q, P, R)`      |
|           | `imp_distrib`       | `Implies(Implies(P, Q, R), P >> Q, P >> R)` |
| 논리곱    | `and_intro`         | `Implies(P, Q, P & Q)`                      |
|           | `and_left`          | `(P & Q) >> P`                              |
|           | `and_right`         | `(P & Q) >> Q`                              |
|           | `and_comm`          | `(P & Q) >> (Q & P)`                        |
|           | `and_assoc`         | `Iff((P & Q) & R, P & (Q & R))`             |
|           | `and_self`          | `Iff(P & P, P)`                             |
| 논리합    | `or_inl`            | `P >> (P \| Q)`                             |
|           | `or_inr`            | `Q >> (P \| Q)`                             |
|           | `or_elim`           | `Implies(P \| Q, P >> R, Q >> R, R)`        |
|           | `or_comm`           | `(P \| Q) >> (Q \| P)`                      |
|           | `or_assoc`          | `Iff((P \| Q) \| R, P \| (Q \| R))`         |
|           | `or_self`           | `Iff(P \| P, P)`                            |
| 분배·커링 | `and_or_distrib`    | `Iff(P & (Q \| R), (P & Q) \| (P & R))`     |
|           | `or_and_distrib`    | `Iff(P \| (Q & R), (P \| Q) & (P \| R))`    |
|           | `curry`             | `Iff((P & Q) >> R, Implies(P, Q, R))`       |
|           | `or_imp`            | `Iff((P \| Q) >> R, (P >> R) & (Q >> R))`   |
| 부정      | `false_elim`        | `Falsehood >> P`                            |
|           | `truth_intro`       | `Truth`                                     |
|           | `explosion`         | `Implies(~P, P, Q)`                         |
|           | `not_contradiction` | `~(P & ~P)`                                 |
|           | `contrapositive`    | `(P >> Q) >> (~Q >> ~P)`                    |
|           | `dni`               | `P >> ~~P`                                  |
|           | `tne`               | `Iff(~~~P, ~P)`                             |
|           | `not_not_em`        | `~~(P \| ~P)`                               |
|           | `not_or`            | `Iff(~(P \| Q), ~P & ~Q)`                   |
|           | `not_and_of_or_not` | `(~P \| ~Q) >> ~(P & Q)`                    |
| 동치      | `iff_refl`          | `Iff(P, P)`                                 |
|           | `iff_symm`          | `Iff(P, Q) >> Iff(Q, P)`                    |
|           | `iff_trans`         | `Implies(Iff(P, Q), Iff(Q, R), Iff(P, R))`  |

- `and_intro`, `and_left`, `or_inl` 등은 증명 문맥의 같은 이름 전방 추론 연산([6.4](#64-전방-추론-연산))과 이름이 같지만, 이 표의 핸들은 `ctx.thm`으로 사용하는 정리이다.
- 표는 v0.1의 최소 집합이다. 정리를 추가할 때는 이 표에 먼저 추가하고, 기존 정리의 이름·명제·순서를 바꾸지 않는 것을 권장한다. 정리의 선언 해시가 바뀌면 그 정리를 참조하는 기존 인증서는 재검증되지 않는다.

## 11. 예제

예제는 비규범적이다. 모든 예제는 다음 머리말을 전제로 한다.

```python
from axiomweave import Prop, Theory, Implies, Falsehood

P, Q, R = (Prop.symbol(name) for name in ("P", "Q", "R"))
thy = Theory("demo.logic")
```

### 11.1. 함의 추이성 (README §4.1의 v0.1 형식)

```python
@thy.theorem
def imp_trans() -> Prop:
    return Implies(P >> Q, Q >> R, P >> R)


@thy.proof(imp_trans)
def _(ctx):
    hpq = ctx.intro()
    hqr = ctx.intro()
    hp = ctx.intro()
    hq = ctx.mp(hpq, hp)
    ctx.exact(ctx.mp(hqr, hq))
```

생성되는 도출은 [logic-spec.md §11.2](logic-spec.md#11-예제)와 같다.

### 11.2. 논리곱 교환 (목표 분할)

```python
@thy.theorem
def and_comm() -> Prop:
    return (P & Q) >> (Q & P)


@thy.proof(and_comm)
def _(ctx):
    h = ctx.intro()
    ctx.split()
    with ctx.focus():
        ctx.exact(ctx.and_right(h))
    with ctx.focus():
        ctx.exact(ctx.and_left(h))
```

### 11.3. 논리합 교환 (경우 분리)

```python
@thy.theorem
def or_comm() -> Prop:
    return (P | Q) >> (Q | P)


@thy.proof(or_comm)
def _(ctx):
    h = ctx.intro()
    hp, hq = ctx.cases(h)
    with ctx.focus():
        ctx.right()
        ctx.exact(hp)
    with ctx.focus():
        ctx.left()
        ctx.exact(hq)
```

### 11.4. 커링 (`apply`)

```python
@thy.theorem
def curry() -> Prop:
    return ((P & Q) >> R) >> Implies(P, Q, R)


@thy.proof(curry)
def _(ctx):
    h = ctx.intro()
    hp = ctx.intro()
    hq = ctx.intro()
    ctx.apply(h)  # 목표: P ∧ Q
    ctx.exact(ctx.and_intro(hp, hq))
```

### 11.5. 정리 인스턴스화

```python
A, B, C = (Prop.symbol(name) for name in ("A", "B", "C"))


@thy.theorem
def and_comm_inst() -> Prop:
    return ((A | B) & C) >> (C & (A | B))


@thy.proof(and_comm_inst)
def _(ctx):
    ctx.exact(ctx.thm(and_comm, {P: A | B, Q: C}))
```

### 11.6. 고전 원리 사용

```python
from axiomweave.lib.logic.classical import classical, em

cthy = Theory("demo.classical", imports=[classical])


@cthy.theorem
def dne_again() -> Prop:
    return ~~P >> P


@cthy.proof(dne_again)
def _(ctx):
    h = ctx.intro()  # h : (P → ⊥) → ⊥
    hp, hnp = ctx.cases(ctx.thm(em))  # P ∨ (P → ⊥)
    with ctx.focus():
        ctx.exact(hp)
    with ctx.focus():
        ctx.exfalso()
        ctx.exact(ctx.mp(h, hnp))


report = cthy.check()  # dne_again.axioms == {"classical.em"}
```

### 11.7. 오류 예

| 코드                                         | 결과                                                          |
| -------------------------------------------- | ------------------------------------------------------------- |
| `if P: ...`                                  | `AxwTypeError` (진릿값 변환)                                  |
| `P & True`                                   | `TypeError` (`Prop`이 아닌 피연산자)                          |
| 목표가 $P \land Q$일 때 `ctx.intro()`        | `TacticError` (목표 형태 불일치)                              |
| 11.3에서 첫 번째 `focus` 안에서 `hq` 사용    | `ScopeError` (`hq`는 두 번째 목표의 가정)                     |
| `ctx.thm(and_comm, {R: C})`                  | `TacticError` ($R \notin \mathrm{atoms}(\mathit{statement})$) |
| 증명 함수가 `split()` 후 첫 목표만 닫고 반환 | 정리 상태 `UNPROVEN`                                          |
| `ctx.thm(t)`에서 `t`가 뒤에 선언된 정리      | `DeclarationError` (선언 순서 위반)                           |

## 12. 단편 L1 DSL

> **상태:** 확정 · 구현됨 (`axiomweave.core.expressions`, `axiomweave.language`). 이 절은 [logic-spec.md §12](logic-spec.md#12-단편-l1-일차-술어-논리)의 L1을 Python DSL로 표현하는 방법을 정의한다. 커널 인코딩은 [kernel-spec.md §13](kernel-spec.md#13-단편-l1-인코딩과-검사)을 따른다. 이 절에서 정하지 않은 사항은 §1–§11을 따른다.

### 12.1. 설계 결정 요약

| 항목             | 결정                                                                                                              |
| ---------------- | ----------------------------------------------------------------------------------------------------------------- |
| 종과 상수        | `thy.sort(name)`, `thy.const(name, args, result)` 호출로 선언한다. 데코레이터가 아니며 호출 순서가 선언 순서이다. |
| 개체 변수        | `Var(name, sort)`. 이름과 종의 쌍으로 식별한다. 이름은 표시용이며, Elaborator가 de Bruijn 인덱스로 바꾼다.        |
| 양화사           | `ForAll(x, A)`, `Exists(x, A)`. 여러 변수는 `ForAll([x, y], A)`로 쓴다 (`ForAll(x, ForAll(y, A))`와 같다).        |
| 스키마 술어 변수 | `Prop.symbol(name, *sorts)`. 인자 종이 없으면 기존 L0 원자이다.                                                   |
| 명제의 `==`      | α-동치이다. 속박 변수 이름만 다른 두 명제는 같다.                                                                 |
| 정리 매개변수    | L1에서는 도입하지 않는다. 정리 선언 함수는 계속 매개변수 없이 닫힌 명제를 반환한다.                        |

README §4.2의 `Symbol(name, Real)` 표기는 비규범적 예시이다. L1은 스키마 변수인 `Prop.symbol`과의 혼동을 피하기 위해 개체 변수를 `Var`로 쓴다.

### 12.2. 종과 상수

```python
from axiomweave import Prop, Theory, Var, ForAll, Exists

thy = Theory("demo.fol")
U = thy.sort("U")                       # 정규 이름 "demo.fol.U"
a = thy.const("a", [], U)               # 개체 상수 a : U
f = thy.const("f", [U], U)              # 함수 기호 f : U → U
Even = thy.const("Even", [U], Prop)     # 술어 기호 Even : U → Prop
```

| API                             | 반환                        | 비고                                                         |
| ------------------------------- | --------------------------- | ------------------------------------------------------------ |
| `thy.sort(name)`                | `Sort`                      | 정규 이름은 `"<theory>.<name>"`                              |
| `thy.const(name, args, result)` | `Const`, 또는 `Term`/`Prop` | `args`는 `Sort`의 목록, `result`는 `Sort` 또는 `Prop` 클래스 |

- `args`가 비어 있으면 반환값은 그 상수를 나타내는 `Term`(결과가 종일 때) 또는 `Prop`(결과가 `Prop`일 때)이다. 인자가 있으면 호출 가능한 `Const`를 반환하며, `f(t)`는 `Term`, `Even(t)`는 `Prop`을 만든다.
- 인자의 수나 종이 맞지 않거나 인자가 `Term`이 아니면 `AxwTypeError`를 일으켜야 한다.
- 다른 Theory에 선언된 종과 상수는 그 Theory를 가져온(imports) 경우에만 사용할 수 있다. 환경에 없는 종이나 상수를 쓴 명제를 선언하면 `DeclarationError`를 일으켜야 한다.
- 선언 이름 규칙과 중복 검사는 [5.1](#51-생성)을 따른다. 종, 상수, 공리, 정리는 같은 이름 공간을 쓴다.

### 12.3. 변수, 항, 양화사

```python
x, y = Var("x", U), Var("y", U)

ForAll(x, Even(x) >> Even(f(f(x))))
Exists(x, Even(x) & ~Even(f(x)))
```

| API               | 의미                                                                |
| ----------------- | ------------------------------------------------------------------- |
| `Var(name, sort)` | 종이 `sort`인 개체 변수. 이름 구문은 [4.2](#42-원자와-상수)와 같다. |
| `ForAll(v, A)`    | $\forall v{:}S.\, A$. `v`는 `Var` 또는 `Var`의 비어 있지 않은 목록  |
| `Exists(v, A)`    | $\exists v{:}S.\, A$                                                |
| `t.sort`          | 항의 종                                                             |

- `Var` 객체는 `(name, sort)`로 식별한다. `ForAll(x, A)`는 `A` 안의 같은 이름·같은 종 변수를 모두 속박한다.
- 한 명제 안에서 같은 이름이 서로 다른 종의 변수로 쓰이면 `AxwTypeError`를 일으켜야 한다.
- 자유 변수를 포함한 `Prop`도 만들 수 있다. 그러나 정리와 공리의 명제는 닫혀 있어야 하며, 자유 변수가 있으면 `DeclarationError`를 일으켜야 한다.
- `Term`에는 `bool()` 변환, 산술·비교 연산자를 정의하지 않는다 (등식은 L2).
- `str(A)`는 `∀x:U, …`가 아니라 `∀x:U. …` 형식을 사용하며, 양화사의 범위는 가능한 한 오른쪽으로 확장된다. 표시는 `Var`의 이름을 사용하고, 충돌하면 결정적 규칙으로 이름을 바꾸어 표시한다.

### 12.4. 스키마 술어 변수

```python
P = Prop.symbol("P", U)        # P : U → Prop (스키마)
Q0 = Prop.symbol("Q")          # 기존 L0 원자

ForAll(x, P(x) >> P(x))
```

- `Prop.symbol(name, *sorts)`는 `sorts`가 비어 있으면 L0와 같은 `Prop`을, 아니면 호출 가능한 `PredicateSymbol`을 반환한다.
- 스키마 변수는 `(name, sorts)`로 식별한다. 정리나 공리의 명제 하나에서 같은 이름을 서로 다른 `sorts`로 쓰면 `DeclarationError`를 일으켜야 한다 (logic-spec §12.6의 이름 유일성).
- 술어 기호(`thy.const(..., Prop)`)와 달리 스키마 변수는 `ctx.thm`의 치환으로 바꿀 수 있다.

### 12.5. 증명 문맥의 확장

**문맥.** 목표의 문맥은 개체 변수 목록과 가정 목록으로 구성된다. 목표 표시는 변수를 먼저 쓴다.

```text
goal 1/1
  y : U
  h : ∀x:U. P(x) ∧ Q(x)
  ⊢ P(y)
```

**목표 전술 (추가·확장)**

| 전술                        | 현재 목표                            | 결과                                                                                        |
| --------------------------- | ------------------------------------ | ------------------------------------------------------------------------------------------- |
| `ctx.intro(name=None)`      | $\forall x{:}S.\, A$                 | 목표를 $\Delta, y : S \vdash A[y/x]$로 바꾸고 변수 $y$의 `Term`을 반환                      |
| `ctx.exists(t)`             | $\exists x{:}S.\, A$                 | `t`의 종이 $S$이면 목표를 $A[t/x]$로 바꿈                                                   |
| `ctx.obtain(f, names=None)` | 임의의 $C$, $f : \exists x{:}S.\, A$ | 목표를 $\Delta, y : S;\ \Gamma, h : A[y/x] \vdash C$로 바꾸고 (`Term` $y$, `Fact` $h$) 반환 |

- `intro`는 목표가 함의이면 기존과 같이 가정을, 전칭이면 변수를 도입한다.
- 변수 이름을 주지 않으면 바인더의 표시 이름을 쓰고, 그 이름이 이 증명에서 이미 쓰였거나 목표의 명제나 가정에서 다른 종의 변수 이름으로 쓰이고 있으면 결정적 규칙(이름 끝의 숫자를 떼고 가장 작은 양의 정수를 붙임)으로 신선한 이름을 만든다. 후자는 한 명제에서 같은 이름이 두 종으로 쓰이지 않게 하기 위한 것이다 ([12.3](#123-변수-항-양화사)). 한 증명 안에서 도입하는 변수 이름은 모두 달라야 한다 ([6.2](#62-가정-이름)과 같은 규칙). 변수와 가정은 서로 다른 이름 공간이다.
- `obtain`의 `names`는 `(변수 이름, 가정 이름)` 쌍이다.

**전방 추론 연산 (추가)**

| 연산                  | 인자                                                     | 결과                          |
| --------------------- | -------------------------------------------------------- | ----------------------------- |
| `ctx.spec(f, *terms)` | $f : \forall x_1 \ldots x_n.\, A$, 항 $t_1, \ldots, t_n$ | $A[t_1/x_1, \ldots, t_n/x_n]$ |

- 목표 전술과 전방 추론 연산에 주는 항과 명제(`exists`, `spec`, `have`, `or_inl`, `absurd` 등의 인자)는 현재 목표의 변수 문맥에서 적격해야 한다. 문맥에 없는 변수를 쓰면 `ScopeError`, 종이 맞지 않으면 `TacticError`를 일으켜야 한다.
- `Fact`와 `intro`/`obtain`이 반환한 변수 `Term`은 만들어진 문맥의 변수와 가정에 의존한다. [6.1](#61-개념)의 범위 규칙은 변수에도 적용된다.

**스키마 치환.** `ctx.thm(decl, subst)`의 `subst`는 L0의 형식에 더해, `PredicateSymbol`을 키로 하고 `(변수 목록, 명제)` 쌍을 값으로 가질 수 있다.

```python
ctx.thm(all_and_left, {P: ([z], Even(z)), Q: ([z], Falsehood)})
```

- 변수 목록의 길이와 종은 키의 `sorts`와 같아야 하며, 그렇지 않으면 `TacticError`를 일으켜야 한다. 명제는 현재 변수 문맥과 이 변수들에서 적격해야 한다.

### 12.6. Elaboration

[7.1](#71-대응-규칙)에 다음을 더한다.

| DSL 연산                 | 생성되는 규칙 적용                              |
| ------------------------ | ----------------------------------------------- |
| `intro` (전칭)           | $\forall\mathrm{I}$ (종)                        |
| `spec` ($n$개 항)        | $\forall\mathrm{E}$를 $n$번                     |
| `exists`                 | $\exists\mathrm{I}$ (술어, 증인)                |
| `obtain`                 | $\exists\mathrm{E}$ (가정 이름)                 |
| `thm` (술어 스키마 치환) | $\mathrm{Thm}$/$\mathrm{Ax}$ (`params` 객체 값) |

- Elaborator는 이름 기반 `Prop`을 kernel-spec §13의 de Bruijn 인코딩으로 변환한다. 같은 `Prop`은 항상 같은 인코딩으로 변환되어야 한다.
- 번들의 `fragment`는 환경에 종 선언이 하나라도 있으면 `"L1"`, 아니면 `"L0"`이다. 상수, 양화사, 인자 있는 스키마 변수는 모두 종을 필요로 하므로, 이는 환경에 L1 구성 요소가 있는지와 같다. 따라서 L0만 쓰는 Theory의 인증서와 해시는 바뀌지 않는다.
- 종과 상수 선언은 `CheckReport.results`에 포함하지 않는다. 결과는 정리만 보고한다 ([5.6](#56-검증)).

### 12.7. 예제

예제는 비규범적이다.

```python
from axiomweave import Exists, ForAll, Prop, Theory, Var

thy = Theory("demo.fol")
U = thy.sort("U")
a = thy.const("a", [], U)
Even = thy.const("Even", [U], Prop)
P, Q = Prop.symbol("P", U), Prop.symbol("Q", U)
x = Var("x", U)


@thy.theorem
def all_and_left() -> Prop:
    return ForAll(x, P(x) & Q(x)) >> ForAll(x, P(x))


@thy.proof(all_and_left)
def _(ctx):
    h = ctx.intro()
    y = ctx.intro()                       # y : U
    ctx.exact(ctx.and_left(ctx.spec(h, y)))


@thy.theorem
def even_witness() -> Prop:
    return Even(a) >> Exists(x, Even(x))


@thy.proof(even_witness)
def _(ctx):
    h = ctx.intro()
    ctx.exists(a)                         # 목표: Even(a)
    ctx.exact(h)


@thy.theorem
def ex_not_all_not() -> Prop:
    return Exists(x, P(x)) >> ~ForAll(x, ~P(x))


@thy.proof(ex_not_all_not)
def _(ctx):
    h1 = ctx.intro()
    h2 = ctx.intro()
    y, hy = ctx.obtain(h1)                # y : U, hy : P(y)
    ctx.exact(ctx.mp(ctx.spec(h2, y), hy))
```

| 오류 예                                                                   | 결과                                |
| ------------------------------------------------------------------------- | ----------------------------------- |
| `@thy.theorem`이 `Even(x)`를 반환 (자유 변수)                             | `DeclarationError`                  |
| `Even(Prop.symbol("R"))`                                                  | `AxwTypeError` (`Term`이 아닌 인자) |
| `split` 뒤 첫 번째 목표에서 `obtain`한 `y`나 `hy`를 두 번째 목표에서 사용 | `ScopeError`                        |
| 목표가 $\exists x{:}U.\, A$일 때 종이 다른 항으로 `ctx.exists(t)`         | `TacticError`                       |

## 13. 단편 L2 DSL

> **상태:** 확정 · 구현됨 (`axiomweave.core.expressions`, `axiomweave.language`). 이 절은 [logic-spec.md §13](logic-spec.md#13-단편-l2-등식)의 등식을 Python DSL로 표현하는 방법을 정의한다. 커널 인코딩은 [kernel-spec.md §14](kernel-spec.md#14-단편-l2-인코딩과-검사)를 따른다. 이 절에서 정하지 않은 사항은 §12를 따른다.

### 13.1. 설계 결정 요약

| 항목                 | 결정                                                                                                   |
| -------------------- | ------------------------------------------------------------------------------------------------------ |
| 등식 생성            | `Eq(t, u)`. 두 인자는 같은 종의 `Term`이어야 한다.                                                     |
| `Term`의 `==`        | 구조적 동일성(`bool`)을 유지한다. 수학적 등식은 `Eq()`로만 만든다 (§2의 `Prop`의 `==`와 같은 원칙).     |
| 연산자               | `Term`에 `==`/`!=` 외의 비교 연산자를 정의하지 않는다. `Ne(t, u)`는 `~Eq(t, u)`의 축약이다.            |
| 전술                 | 목표 전술 `rfl`, `rewrite`와 전방 추론 연산 `refl`, `symm`, `trans`, `congr`, `subst`를 둔다.         |
| 생성되는 규칙        | 모든 전술은 $=\mathrm{I}$와 $=\mathrm{E}$(그리고 기존 규칙)만 생성한다. 대칭 등은 [logic-spec.md §13.5](logic-spec.md#135-파생-규칙)처럼 전개한다. |
| 출현 위치            | `rewrite`, `subst`는 항 $t$의 모든 자유 출현을 바꾼다. 일부만 바꾸려면 `subst`에 동기를 직접 준다.      |

### 13.2. 등식 명제

```python
from axiomweave import Eq, ForAll, Ne, Prop, Theory, Var

thy = Theory("demo.eq")
U = thy.sort("U")
f = thy.const("f", [U], U)
x, y = Var("x", U), Var("y", U)

ForAll([x, y], Eq(x, y) >> Eq(f(x), f(y)))
```

| API          | 의미                                           |
| ------------ | ---------------------------------------------- |
| `Eq(t, u)`   | $t = u$. `t.sort != u.sort`이면 `AxwTypeError` |
| `Ne(t, u)`   | $\lnot(t = u)$, 즉 $(t = u) \to \bot$          |

- `str(Eq(t, u))`는 `t = u`이다. `=`의 우선순위는 술어 적용과 같다 (괄호가 필요 없다).
- `Eq`의 인자가 `Term`이 아니면 (예: `Prop`) `AxwTypeError`를 일으켜야 한다.

### 13.3. 전술

**목표 전술**

| 전술                              | 현재 목표          | 결과                                                                                       |
| --------------------------------- | ------------------ | ------------------------------------------------------------------------------------------ |
| `ctx.rfl()`                       | $t = t$            | 목표를 닫음                                                                                |
| `ctx.rewrite(f, reverse=False)`   | 임의의 $G$, $f : t = u$ | $G$의 $t$의 자유 출현을 모두 $u$로 바꾼 목표 $G'$로 바꿈. `reverse=True`이면 $u$를 $t$로 바꿈 |

- `rewrite`할 항이 목표에 자유롭게 나타나지 않으면 `TacticError`를 일으켜야 한다.
- `rewrite`는 새 목표 $G'$의 증명으로부터 $G$를 얻으므로, 방향을 맞추기 위해 대칭을 한 번 전개한다 ([13.4](#134-elaboration)).

**전방 추론 연산**

| 연산                                    | 인자                                           | 결과                         |
| --------------------------------------- | ---------------------------------------------- | ---------------------------- |
| `ctx.refl(t)`                           | 항 $t$                                         | $t = t$                      |
| `ctx.symm(f)`                           | $f : t = u$                                    | $u = t$                      |
| `ctx.trans(f, g)`                       | $f : t = u$, $g : u = v$                       | $t = v$                      |
| `ctx.congr(f, (x, s))`                  | $f : t = u$, 변수 $x$와 항 $s$                 | $s[t/x] = s[u/x]$            |
| `ctx.subst(f, g, motive=None)`          | $f : t = u$, $g : A$                           | $A$의 $t$를 $u$로 바꾼 명제   |

- `subst`에 `motive=(x, A)`를 주면 $g$는 $A[t/x]$를 증명해야 하며, 결과는 $A[u/x]$이다. 주지 않으면 $g$의 명제에서 $t$의 모든 자유 출현을 새 변수로 추상한 것을 동기로 쓴다.
- `trans`에서 $f$의 오른쪽과 $g$의 왼쪽이 같지 않으면, `congr`에서 `x`가 변수가 아니거나 `s`와 종이 맞지 않으면 `TacticError`를 일으켜야 한다.
- 인자 항과 동기는 [12.5](#125-증명-문맥의-확장)의 범위 규칙을 따른다.

**자유 출현.** 명제 $A$에서 항 $t$의 자유 출현은 $A$의 부분 항 중 $t$와 같고, 그 위치에서 $t$의 자유 변수가 어느 바인더에도 속박되지 않은 것이다. 추상은 그 위치들을 바인더에 속박되지 않는 새 변수로 바꾼다.

### 13.4. Elaboration

[12.6](#126-elaboration)에 다음을 더한다.

| DSL 연산        | 생성되는 규칙 적용                                                                           |
| --------------- | -------------------------------------------------------------------------------------------- |
| `rfl`, `refl`   | $=\mathrm{I}$                                                                                |
| `symm`          | $=\mathrm{E}$ (동기 $\lambda z.\, z = t$, $f$, $=\mathrm{I}\ t$)                           |
| `trans`         | $=\mathrm{E}$ (동기 $\lambda z.\, t = z$, $g$, $f$)                                         |
| `congr`         | $=\mathrm{E}$ (동기 $\lambda z.\, s[t/x] = s[z/x]$, $f$, $=\mathrm{I}\ s[t/x]$)            |
| `subst`         | $=\mathrm{E}$ (동기, $f$, $g$)                                                               |
| `rewrite`       | $=\mathrm{E}$ (동기 $G$의 추상, `symm` $f$, 새 목표). `reverse=True`이면 `symm` 없이 $f$     |

- 번들의 `fragment`는 환경의 명제나 도출에 등식(`eq`, `eq_refl`, `eq_e`)이 하나라도 있으면 `"L2"`이고, 그렇지 않으면 [12.6](#126-elaboration)의 규칙을 따른다. 따라서 등식을 쓰지 않는 L1 Theory의 인증서는 바뀌지 않는다.

### 13.5. 예제

예제는 비규범적이다.

```python
from axiomweave import Eq, ForAll, Prop, Theory, Var

thy = Theory("demo.eq")
U = thy.sort("U")
f = thy.const("f", [U], U)
Even = thy.const("Even", [U], Prop)
x, y, z = Var("x", U), Var("y", U), Var("z", U)


@thy.theorem
def eq_symm() -> Prop:
    return ForAll([x, y], Eq(x, y) >> Eq(y, x))


@thy.proof(eq_symm)
def _(ctx):
    ctx.intro()
    ctx.intro()
    h = ctx.intro()
    ctx.exact(ctx.symm(h))


@thy.theorem
def even_congr() -> Prop:
    return ForAll([x, y], Eq(x, y) >> (Even(f(x)) >> Even(f(y))))


@thy.proof(even_congr)
def _(ctx):
    ctx.intro()
    ctx.intro()
    h = ctx.intro()
    he = ctx.intro()
    ctx.rewrite(h, reverse=True)     # 목표: Even(f(x))
    ctx.exact(he)


@thy.theorem
def eq_trans() -> Prop:
    return ForAll([x, y, z], Eq(x, y) >> (Eq(y, z) >> Eq(x, z)))


@thy.proof(eq_trans)
def _(ctx):
    ctx.intro(); ctx.intro(); ctx.intro()
    h1 = ctx.intro()
    h2 = ctx.intro()
    ctx.exact(ctx.trans(h1, h2))
```

| 오류 예                                              | 결과                                             |
| ---------------------------------------------------- | ------------------------------------------------ |
| 종이 다른 두 항으로 `Eq(a, b)`                       | `AxwTypeError`                                   |
| `Eq(Prop.symbol("P"), Prop.symbol("Q"))`             | `AxwTypeError`                                   |
| 목표가 $f(a) = a$일 때 `ctx.rfl()`                   | `TacticError`                                    |
| 목표에 없는 항으로 `ctx.rewrite(h)`                   | `TacticError`                                    |
| `ctx.trans(f, g)`에서 가운데 항이 다름               | `TacticError`                                    |

## 14. 단계 L3 DSL: 자연수

> **상태:** 확정 · 구현됨 (`axiomweave.lib.arithmetic.peano`, `ctx.induction`). 이 절은 [logic-spec.md §14](logic-spec.md#14-단계-l3-자연수와-귀납)의 표준 산술 Theory를 Python DSL로 제공하는 방법을 정의한다. 이 절에서 정하지 않은 사항은 §13을 따른다.

### 14.1. 설계 결정 요약

| 항목            | 결정                                                                                                   |
| --------------- | ------------------------------------------------------------------------------------------------------ |
| 제공 위치       | 표준 Theory `arith`를 `axiomweave.lib.arithmetic.peano` 모듈로 제공한다 (§10의 표준 Theory와 같은 방식). |
| 산술 표기       | 연산자를 오버로드하지 않는다. `add(m, n)`, `mul(m, n)`, `succ(n)`, `zero`를 쓴다.                       |
| 수 표기         | `numeral(k)`는 $S^k(0)$을 만든다. 커널에는 수 리터럴이 없다.                                           |
| 귀납 전술       | `ctx.induction()`은 `arith.induction` 공리의 인스턴스로 Elaboration된다. 새 커널 규칙을 만들지 않는다.   |
| 라이브러리 정리 | `arith`는 공리 외에 덧셈의 기본 정리를 증명하여 제공한다 ([14.3](#143-표준-theory-arith)).              |

### 14.2. 사용

```python
from axiomweave import Eq, ForAll, Prop, Theory, Var
from axiomweave.lib.arithmetic.peano import Nat, add, arith, numeral, succ, zero

thy = Theory("demo.nat", imports=[arith])
n = Var("n", Nat)


@thy.theorem
def zero_add_example() -> Prop:
    return ForAll(n, Eq(add(zero, n), n))
```

- 산술 공리와 정리를 쓰는 Theory는 `arith`를 가져와야 한다 ([12.2](#122-종과-상수)).
- `numeral(k)`는 `k`가 0 이상의 Python `int`일 때만 허용한다. 그 밖의 값은 `AxwTypeError`이다. `bool`은 허용하지 않는다.

### 14.3. 표준 Theory `arith`

```python
from axiomweave.lib.arithmetic.peano import arith, Nat, zero, succ, add, mul, numeral
```

| 핸들           | 종류      | 정규 이름              | 내용                                    |
| -------------- | --------- | ---------------------- | --------------------------------------- |
| `Nat`          | `Sort`    | `arith.Nat`            |                                         |
| `zero`         | `Term`    | `arith.zero`           | $0$                                     |
| `succ`         | `Const`   | `arith.succ`           | $S$                                     |
| `add`, `mul`   | `Const`   | `arith.add`, `arith.mul` | $+$, $\times$                         |
| `succ_ne_zero` 등 7개 | `Axiom` | `arith.succ_ne_zero` 등 | [logic-spec.md §14.3](logic-spec.md#143-표준-선언)의 공리 |
| `zero_add`     | `Theorem` | `arith.zero_add`       | $\forall n.\, 0 + n = n$                |
| `succ_add`     | `Theorem` | `arith.succ_add`       | $\forall m\, n.\, S(m) + n = S(m + n)$  |
| `add_comm`     | `Theorem` | `arith.add_comm`       | $\forall m\, n.\, m + n = n + m$        |
| `add_assoc`    | `Theorem` | `arith.add_assoc`      | $\forall k\, m\, n.\, (k + m) + n = k + (m + n)$ |

- 선언 순서는 표의 순서(종, 상수, 공리, 정리)이다. 종, 상수, 공리의 이름과 명제는 kernel-spec §15의 표준 해시와 정확히 일치해야 한다.
- 정리는 일반 증명으로 검증되며, 의존 공리 집합에 사용한 `arith.*` 공리가 기록된다. 이 Theory의 정리는 `classical.em`에 의존해서는 안 된다.

### 14.4. 귀납 전술

| 전술                            | 현재 목표                         | 결과                                                                                      |
| ------------------------------- | --------------------------------- | ----------------------------------------------------------------------------------------- |
| `ctx.induction()`               | $\forall n{:}\mathit{Nat}.\, A$    | 목표를 $A[0/n]$와 $\forall n{:}\mathit{Nat}.\, A \to A[S(n)/n]$ 두 개로 바꿈 (이 순서)    |

- 목표가 종 `arith.Nat`에 대한 전칭이 아니면 `TacticError`를 일으켜야 한다.
- 전술은 공리를 정규 이름 `arith.induction`으로 현재 Theory의 환경에서 찾는다. 따라서 라이브러리 모듈이 어떤 경로로 로드되었든 환경에 있는 `arith`를 사용한다. 환경에 없으면 `DeclarationError`를 일으켜야 한다.
- Elaboration: `arith.induction`을 $P \mapsto \lambda n.\, A$로 인스턴스화하는 $\mathrm{Ax}$와 두 번의 $\to\mathrm{E}$이다. $A$에 현재 문맥의 변수가 있어도 된다.
- 귀납 단계 목표는 `intro`로 변수와 귀납 가정을 도입하여 증명한다.

### 14.5. 예제

예제는 비규범적이다.

```python
@arith.proof(zero_add)
def _(ctx):
    ctx.induction()
    with ctx.focus():                      # 0 + 0 = 0
        ctx.exact(ctx.spec(ctx.thm(add_zero), zero))
    with ctx.focus():                      # ∀n. 0 + n = n → 0 + S(n) = S(n)
        n = ctx.intro()
        ih = ctx.intro()
        step = ctx.spec(ctx.thm(add_succ), zero, n)   # 0 + S(n) = S(0 + n)
        ctx.rewrite(step)                  # 목표: S(0 + n) = S(n)
        ctx.rewrite(ih)                    # 목표: S(n) = S(n)
        ctx.rfl()
```

| 오류 예                                            | 결과                 |
| -------------------------------------------------- | -------------------- |
| 목표가 $\forall x{:}U.\, A$ ($U \ne \mathit{Nat}$)일 때 `ctx.induction()` | `TacticError` |
| `arith`를 가져오지 않은 Theory에서 `ctx.induction()` | `DeclarationError` (증명 상태 `REJECTED`) |
| `numeral(-1)`, `numeral(True)`                     | `AxwTypeError`       |

## 15. 확장 시 유의 사항

이 절은 L4 이후 개정을 위한 비규범적 메모이다.

- 매개변수를 받는 정리 선언(README §4.3)은 L1–L3에 포함하지 않았다. 도입한다면 `def t(x: U)`의 매개변수를 전칭 양화로 해석하고, 정리의 적용 `t(a)`를 `ctx.spec`으로 Elaboration하는 방식을 검토한다. `@thy.definition`의 본문을 실행하지 않고 제한된 구문으로 변환하는 방식(proposal §5.5)도 함께 검토한다.
- `unfold` 등 전술과 자동화 전술은 해당 논리 단편이 도입된 뒤 이 문서에 추가한다. 자동화 전술도 이 문서의 전술과 마찬가지로 [7.1](#71-대응-규칙), [12.6](#126-elaboration), [13.4](#134-elaboration), [14.4](#144-귀납-전술)의 규칙 적용만 생성해야 한다.
- 정적 린트 도구는 [4.5](#45-연산자-우선순위와-괄호-규칙)의 괄호 규칙 위반을 Python AST에서 검출할 수 있다.
